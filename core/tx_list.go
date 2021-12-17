// Copyright 2016 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package core

import (
	"container/heap"
	"math/big"
	"sync"
	"sync/atomic"
	"time"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/types"
)

// txSortedList is sorted list (by nonce) of transactions
type txSortedList types.Transactions

// newTxSortedList creates a new nonce-sorted transaction map.
func newTxSortedList() *txSortedList {
	txs := make(txSortedList, 0)
	return &txs
}

// Get retrieves the current transactions associated with the given nonce.
func (m *txSortedList) Get(nonce uint64) *types.Transaction {
	index, _, _ := m.FindIndex(nonce)
	if index == -1 {
		return nil
	}

	return (*m)[index]
}

// Check if transactions associated with the given nonce exists
func (m *txSortedList) Contains(nonce uint64) bool {
	index, _, _ := m.FindIndex(nonce)
	return index != -1
}

// Put inserts a new transaction into sorted list at position defined by nonce
// If transaction already exists with the same nonce, it's overwritten.
func (m *txSortedList) Put(tx *types.Transaction) {
	index, _, insertIndex := m.FindIndex(tx.Nonce())
	if index != -1 {
		(*m)[index] = tx
	} else if insertIndex == len(*m) {
		*m = append(*m, tx)
	} else {
		// index < len(a)
		*m = append((*m)[:insertIndex+1], (*m)[insertIndex:]...)
		(*m)[insertIndex] = tx
	}
}

// Forward removes all transactions from the sorted list with a nonce lower than the provided threshold.
// Every removed transaction is returned for any post-removal maintenance.
func (m *txSortedList) Forward(nonceThreshold uint64) types.Transactions {
	_, lowerNonceIndex, _ := m.FindIndex(nonceThreshold)
	removed := types.Transactions((*m)[0 : lowerNonceIndex+1])
	*m = (*m)[lowerNonceIndex+1 : len(*m)]
	return removed
}

// Filter iterates over the list of transactions and removes all of them for which
// the specified function evaluates to true.
func (m *txSortedList) Filter(filter func(*types.Transaction) bool) types.Transactions {
	var removed types.Transactions
	index := 0

	// Collect all the transactions to filter out
	for _, tx := range *m {
		if filter(tx) {
			removed = append(removed, tx)
		} else {
			(*m)[index] = tx
			index++
		}
	}
	*m = (*m)[0:index]
	return removed
}

// Cap places a hard limit on the number of items, returning all transactions
// exceeding that limit.
func (m *txSortedList) Cap(threshold int) types.Transactions {
	// Short circuit if the number of items is under the limit
	if len(*m) <= threshold {
		return nil
	}
	// Otherwise gather and drop the highest nonce'd transactions
	drops := types.Transactions((*m)[threshold:len(*m)])
	*m = (*m)[0:threshold]
	return drops
}

// Binary search through txSortedList and find:
// - position of transaction with nonce,
// - position of first lower nonce and
// - position where new transaction with given nonce should be inserted.
func (m *txSortedList) FindIndex(nonce uint64) (index int, leftIndex int, rightIndex int) {
	low, high := 0, len(*m)-1
	index, leftIndex, rightIndex = -1, -1, len(*m)
	for low <= high {
		median := low + (high-low)>>1
		if (*m)[median].Nonce() < nonce {
			leftIndex = median
			low = median + 1
		} else {
			rightIndex = median
			high = median - 1
		}
	}

	if low < len(*m) && (*m)[low].Nonce() == nonce {
		index = low
	}

	return index, leftIndex, rightIndex
}

// Remove deletes a transaction, returning whether the transaction was found.
func (m *txSortedList) Remove(nonce uint64) bool {
	index, _, _ := m.FindIndex(nonce)
	if index == -1 {
		return false
	}
	*m = append((*m)[0:index], (*m)[index+1:len(*m)]...)
	return true
}

// Ready retrieves a sequentially increasing list of transactions starting at the
// provided nonce that is ready for processing. The returned transactions will be
// removed from the list.
//
// Note, all transactions with nonces lower than start will also be returned to
// prevent getting into and invalid state. This is not something that should ever
// happen but better to be self correcting than failing!
func (m *txSortedList) Ready(start uint64) types.Transactions {
	// Short circuit if no transactions are available
	if len(*m) == 0 || (*m)[0].Nonce() > start {
		return nil
	}
	// Otherwise start accumulating incremental transactions
	i, next := 0, (*m)[0].Nonce()
	for i < len(*m) && (*m)[i].Nonce() == next {
		i++
		next++
	}

	ready := types.Transactions((*m)[0:i])
	*m = (*m)[i:len(*m)]
	return ready
}

// Len returns the length of the transaction map.
func (m *txSortedList) Len() int {
	return len(*m)
}

// Flatten creates a nonce-sorted slice of transactions based on the loosely sorted internal representation.
func (m *txSortedList) Flatten() types.Transactions {
	// Copy the cache to prevent accidental modifications
	txs := make(types.Transactions, len(*m))
	copy(txs, *m)
	return txs
}

// LastElement returns the last element of a flattened list, thus, the
// transaction with the highest nonce
func (m *txSortedList) LastElement() *types.Transaction {
	return (*m)[len(*m)-1]
}

// txList is a "list" of transactions belonging to an account, sorted by account
// nonce. The same type can be used both for storing contiguous transactions for
// the executable/pending queue; and for storing gapped transactions for the non-
// executable/future queue, with minor behavioral changes.
type txList struct {
	strict bool          // Whether nonces are strictly continuous or not
	txs    *txSortedList // Nonces-sorted list of the transactions

	costcap *big.Int // Price of the highest costing transaction (reset only if exceeds balance)
	gascap  uint64   // Gas limit of the highest spending transaction (reset only if exceeds block limit)
}

// newTxList create a new transaction list for maintaining nonce-indexable fast,
// gapped, sortable transaction lists.
func newTxList(strict bool) *txList {
	return &txList{
		strict:  strict,
		txs:     newTxSortedList(),
		costcap: new(big.Int),
	}
}

// Overlaps returns whether the transaction specified has the same nonce as one
// already contained within the list.
func (l *txList) Overlaps(tx *types.Transaction) bool {
	return l.txs.Contains(tx.Nonce())
}

// Add tries to insert a new transaction into the list, returning whether the
// transaction was accepted, and if yes, any previous transaction it replaced.
//
// If the new transaction is accepted into the list, the lists' cost and gas
// thresholds are also potentially updated.
func (l *txList) Add(tx *types.Transaction, priceBump uint64) (bool, *types.Transaction) {
	// If there's an older better transaction, abort
	old := l.txs.Get(tx.Nonce())
	if old != nil {
		if old.GasFeeCapCmp(tx) >= 0 || old.GasTipCapCmp(tx) >= 0 {
			return false, nil
		}
		// thresholdFeeCap = oldFC  * (100 + priceBump) / 100
		a := big.NewInt(100 + int64(priceBump))
		aFeeCap := new(big.Int).Mul(a, old.GasFeeCap())
		aTip := a.Mul(a, old.GasTipCap())

		// thresholdTip    = oldTip * (100 + priceBump) / 100
		b := big.NewInt(100)
		thresholdFeeCap := aFeeCap.Div(aFeeCap, b)
		thresholdTip := aTip.Div(aTip, b)

		// Have to ensure that either the new fee cap or tip is higher than the
		// old ones as well as checking the percentage threshold to ensure that
		// this is accurate for low (Wei-level) gas price replacements
		if tx.GasFeeCapIntCmp(thresholdFeeCap) < 0 || tx.GasTipCapIntCmp(thresholdTip) < 0 {
			return false, nil
		}
	}
	// Otherwise overwrite the old transaction with the current one
	l.txs.Put(tx)
	if cost := tx.Cost(); l.costcap.Cmp(cost) < 0 {
		l.costcap = cost
	}
	if gas := tx.Gas(); l.gascap < gas {
		l.gascap = gas
	}
	return true, old
}

// Forward removes all transactions from the list with a nonce lower than the
// provided threshold. Every removed transaction is returned for any post-removal
// maintenance.
func (l *txList) Forward(threshold uint64) types.Transactions {
	return l.txs.Forward(threshold)
}

// Filter removes all transactions from the list with a cost or gas limit higher
// than the provided thresholds. Every removed transaction is returned for any
// post-removal maintenance. Strict-mode invalidated transactions are also
// returned.
//
// This method uses the cached costcap and gascap to quickly decide if there's even
// a point in calculating all the costs or if the balance covers all. If the threshold
// is lower than the costgas cap, the caps will be reset to a new high after removing
// the newly invalidated transactions.
func (l *txList) Filter(costLimit *big.Int, gasLimit uint64) (types.Transactions, types.Transactions) {
	// If all transactions are below the threshold, short circuit
	if l.costcap.Cmp(costLimit) <= 0 && l.gascap <= gasLimit {
		return nil, nil
	}
	l.costcap = new(big.Int).Set(costLimit) // Lower the caps to the thresholds
	l.gascap = gasLimit

	// Filter out all the transactions above the account's funds
	removed := l.txs.Filter(func(tx *types.Transaction) bool {
		return tx.Gas() > gasLimit || tx.Cost().Cmp(costLimit) > 0
	})

	if len(removed) == 0 {
		return nil, nil
	}
	var invalids types.Transactions
	// If the list was strict, filter anything above the lowest nonce
	if l.strict {
		lowestRemovedNonce := removed[0].Nonce()
		invalids = l.txs.Filter(func(tx *types.Transaction) bool { return tx.Nonce() > lowestRemovedNonce })
	}
	return removed, invalids
}

// Cap places a hard limit on the number of items, returning all transactions
// exceeding that limit.
func (l *txList) Cap(threshold int) types.Transactions {
	return l.txs.Cap(threshold)
}

// Remove deletes a transaction from the maintained list, returning whether the
// transaction was found, and also returning any transaction invalidated due to
// the deletion (strict mode only).
func (l *txList) Remove(tx *types.Transaction) (bool, types.Transactions) {
	// Remove the transaction from the set
	nonce := tx.Nonce()
	if removed := l.txs.Remove(nonce); !removed {
		return false, nil
	}
	// In strict mode, filter out non-executable transactions
	if l.strict {
		return true, l.txs.Filter(func(tx *types.Transaction) bool { return tx.Nonce() > nonce })
	}
	return true, nil
}

// Ready retrieves a sequentially increasing list of transactions starting at the
// provided nonce that is ready for processing. The returned transactions will be
// removed from the list.
//
// Note, all transactions with nonces lower than start will also be returned to
// prevent getting into and invalid state. This is not something that should ever
// happen but better to be self correcting than failing!
func (l *txList) Ready(start uint64) types.Transactions {
	return l.txs.Ready(start)
}

// Len returns the length of the transaction list.
func (l *txList) Len() int {
	return l.txs.Len()
}

// Empty returns whether the list of transactions is empty or not.
func (l *txList) Empty() bool {
	return l.Len() == 0
}

// Flatten creates a nonce-sorted slice of transactions based on the loosely
// sorted internal representation. The result of the sorting is cached in case
// it's requested again before any modifications are made to the contents.
func (l *txList) Flatten() types.Transactions {
	return l.txs.Flatten()
}

// LastElement returns the last element of a flattened list, thus, the
// transaction with the highest nonce
func (l *txList) LastElement() *types.Transaction {
	return l.txs.LastElement()
}

// priceHeap is a heap.Interface implementation over transactions for retrieving
// price-sorted transactions to discard when the pool fills up. If baseFee is set
// then the heap is sorted based on the effective tip based on the given base fee.
// If baseFee is nil then the sorting is based on gasFeeCap.
type priceHeap struct {
	baseFee *big.Int // heap should always be re-sorted after baseFee is changed
	list    []*types.Transaction
}

func (h *priceHeap) Len() int      { return len(h.list) }
func (h *priceHeap) Swap(i, j int) { h.list[i], h.list[j] = h.list[j], h.list[i] }

func (h *priceHeap) Less(i, j int) bool {
	switch h.cmp(h.list[i], h.list[j]) {
	case -1:
		return true
	case 1:
		return false
	default:
		return h.list[i].Nonce() > h.list[j].Nonce()
	}
}

func (h *priceHeap) cmp(a, b *types.Transaction) int {
	if h.baseFee != nil {
		// Compare effective tips if baseFee is specified
		if c := a.EffectiveGasTipCmp(b, h.baseFee); c != 0 {
			return c
		}
	}
	// Compare fee caps if baseFee is not specified or effective tips are equal
	if c := a.GasFeeCapCmp(b); c != 0 {
		return c
	}
	// Compare tips if effective tips and fee caps are equal
	return a.GasTipCapCmp(b)
}

func (h *priceHeap) Push(x interface{}) {
	tx := x.(*types.Transaction)
	h.list = append(h.list, tx)
}

func (h *priceHeap) Pop() interface{} {
	old := h.list
	n := len(old)
	x := old[n-1]
	old[n-1] = nil
	h.list = old[0 : n-1]
	return x
}

// txPricedList is a price-sorted heap to allow operating on transactions pool
// contents in a price-incrementing way. It's built opon the all transactions
// in txpool but only interested in the remote part. It means only remote transactions
// will be considered for tracking, sorting, eviction, etc.
//
// Two heaps are used for sorting: the urgent heap (based on effective tip in the next
// block) and the floating heap (based on gasFeeCap). Always the bigger heap is chosen for
// eviction. Transactions evicted from the urgent heap are first demoted into the floating heap.
// In some cases (during a congestion, when blocks are full) the urgent heap can provide
// better candidates for inclusion while in other cases (at the top of the baseFee peak)
// the floating heap is better. When baseFee is decreasing they behave similarly.
type txPricedList struct {
	// Number of stale price points to (re-heap trigger).
	// This field is accessed atomically, and must be the first field
	// to ensure it has correct alignment for atomic.AddInt64.
	// See https://golang.org/pkg/sync/atomic/#pkg-note-BUG.
	stales int64

	all              *txLookup  // Pointer to the map of all transactions
	urgent, floating priceHeap  // Heaps of prices of all the stored **remote** transactions
	reheapMu         sync.Mutex // Mutex asserts that only one routine is reheaping the list
}

const (
	// urgentRatio : floatingRatio is the capacity ratio of the two queues
	urgentRatio   = 4
	floatingRatio = 1
)

// newTxPricedList creates a new price-sorted transaction heap.
func newTxPricedList(all *txLookup) *txPricedList {
	return &txPricedList{
		all: all,
	}
}

// Put inserts a new transaction into the heap.
func (l *txPricedList) Put(tx *types.Transaction, local bool) {
	if local {
		return
	}
	// Insert every new transaction to the urgent heap first; Discard will balance the heaps
	heap.Push(&l.urgent, tx)
}

// Removed notifies the prices transaction list that an old transaction dropped
// from the pool. The list will just keep a counter of stale objects and update
// the heap if a large enough ratio of transactions go stale.
func (l *txPricedList) Removed(count int) {
	// Bump the stale counter, but exit if still too low (< 25%)
	stales := atomic.AddInt64(&l.stales, int64(count))
	if int(stales) <= (len(l.urgent.list)+len(l.floating.list))/4 {
		return
	}
	// Seems we've reached a critical number of stale transactions, reheap
	l.Reheap()
}

// Underpriced checks whether a transaction is cheaper than (or as cheap as) the
// lowest priced (remote) transaction currently being tracked.
func (l *txPricedList) Underpriced(tx *types.Transaction) bool {
	// Note: with two queues, being underpriced is defined as being worse than the worst item
	// in all non-empty queues if there is any. If both queues are empty then nothing is underpriced.
	return l.underpricedFor(&l.urgent, tx) && l.underpricedFor(&l.floating, tx)
}

// underpricedFor checks whether a transaction is cheaper than (or as cheap as) the
// lowest priced (remote) transaction in the given heap.
func (l *txPricedList) underpricedFor(h *priceHeap, tx *types.Transaction) bool {
	// Discard stale price points if found at the heap start
	for len(h.list) > 0 && l.all.GetRemote(h.list[0].Hash()) == nil {
		// Removed or migrated
		atomic.AddInt64(&l.stales, -1)
		heap.Pop(h)
	}
	// If the remote transaction is even cheaper than the
	// cheapest one tracked locally, reject it.
	return len(h.list) == 0 || h.cmp(h.list[0], tx) >= 0
}

// Discard finds a number of most underpriced transactions, removes them from the
// priced list and returns them for further removal from the entire pool.
//
// Note local transaction won't be considered for eviction.
func (l *txPricedList) Discard(slots int, force bool) (types.Transactions, bool) {
	drop := make(types.Transactions, 0, slots) // Remote underpriced transactions to drop
	for slots > 0 {
		if len(l.urgent.list)*floatingRatio > len(l.floating.list)*urgentRatio || floatingRatio == 0 {
			// Discard stale transactions if found during cleanup
			tx := heap.Pop(&l.urgent).(*types.Transaction)
			if l.all.GetRemote(tx.Hash()) == nil { // Removed or migrated
				atomic.AddInt64(&l.stales, -1)
				continue
			}
			// Non stale transaction found, move to floating heap
			heap.Push(&l.floating, tx)
		} else {
			if len(l.floating.list) == 0 {
				// Stop if both heaps are empty
				break
			}
			// Discard stale transactions if found during cleanup
			tx := heap.Pop(&l.floating).(*types.Transaction)
			if l.all.GetRemote(tx.Hash()) == nil { // Removed or migrated
				atomic.AddInt64(&l.stales, -1)
				continue
			}
			// Non stale transaction found, discard it
			drop = append(drop, tx)
			slots -= numSlots(tx)
		}
	}
	// If we still can't make enough room for the new transaction
	if slots > 0 && !force {
		for _, tx := range drop {
			// FIXME: Bug? Always pushing to the urgent, although it is retrieved from floating heap whereas the transaction could be originating either from urgent or floating.
			// We should be tracking where transaction originated from (urgent or floating) and revert it to appropriate heap.
			heap.Push(&l.urgent, tx)
		}
		return nil, false
	}
	return drop, true
}

// Reheap forcibly rebuilds the heap based on the current remote transaction set.
func (l *txPricedList) Reheap() {
	l.reheapMu.Lock()
	defer l.reheapMu.Unlock()
	start := time.Now()
	atomic.StoreInt64(&l.stales, 0)
	l.urgent.list = make([]*types.Transaction, 0, l.all.RemoteCount())
	l.all.Range(func(hash common.Hash, tx *types.Transaction, local bool) bool {
		l.urgent.list = append(l.urgent.list, tx)
		return true
	}, false, true) // Only iterate remotes
	heap.Init(&l.urgent)

	// balance out the two heaps by moving the worse half of transactions into the
	// floating heap
	// Note: Discard would also do this before the first eviction but Reheap can do
	// is more efficiently. Also, Underpriced would work suboptimally the first time
	// if the floating queue was empty.

	// FIXME: Floating heap must be kept at least 25% of urgent heap size (see Discard function)?
	// This way it is only 20% of urgent heap size.
	floatingCount := len(l.urgent.list) * floatingRatio / (urgentRatio + floatingRatio)
	l.floating.list = make([]*types.Transaction, floatingCount)
	for i := 0; i < floatingCount; i++ {
		l.floating.list[i] = heap.Pop(&l.urgent).(*types.Transaction)
	}
	heap.Init(&l.floating)
	reheapTimer.Update(time.Since(start))
}

// SetBaseFee updates the base fee and triggers a re-heap. Note that Removed is not
// necessary to call right before SetBaseFee when processing a new block.
func (l *txPricedList) SetBaseFee(baseFee *big.Int) {
	l.urgent.baseFee = baseFee
	l.Reheap()
}
