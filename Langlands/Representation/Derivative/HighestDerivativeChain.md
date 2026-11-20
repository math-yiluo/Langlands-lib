# Level sequences and iterated derivative chains

These are internal definitions and lemmas for the proof of the irreducibility assertion in
Zelevinsky (1980), Theorem 8.1. They encode a test on successive actual derivatives, not a
classification of multisegments or their representations. The sequence packages the
simultaneous last-endpoint truncation of segments used in Zelevinsky's §6.6.

For a multisegment `a`, `levelAt j a` sums the cuspidal ranks of its segments of length
strictly greater than `j`, counted with multiplicity. `maxLength a` is the largest segment
length, with value zero for the empty multisegment. `levelSequence a` lists the levels
starting at `j = 0` and stopping before `maxLength a`. For nonempty `a` its head is the total
cuspidal rank, and its tail is the sequence for `a.filterMap Segment.dropLast`. The proof
compares the levels and maximum lengths before and after truncation by multiset induction,
distinguishing segments of length one (which disappear) from longer segments. Mapping
segments by a function that preserves rank and length preserves the sequence.

`DerivativeChain T ψ s n W` checks the orders in the list `s` from left to right: each
order `k` must be positive and at most the current rank, and the next representation is
the actual `generalLinearDerivative` of order `k` on `GL_(n-k)`. The empty list requires
that the current representation be nonzero, so the predicate tests nonvanishing of the
**final** representation with all orders legal. Invariance under isomorphism follows
by induction using the derivative functor's action on isomorphisms. Invariance under
a real determinant twist uses the published `generalLinearDerivativeDeterminantTwist`
comparison at each step, followed by the same induction on the remaining orders.
