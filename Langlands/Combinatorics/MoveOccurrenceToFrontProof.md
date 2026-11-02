# Adjacent transport of a specified original occurrence

Worker 320's internal proof of `MoveOccurrenceToFront` uses an explicit
permutation `moveToPosition i k`. It places original label `i` at position `k`,
moves each original label `j` with `k ≤ j < i` to new position `j+1`, and fixes
every other original label. Thus new positions `k+1` through `i` contain
original labels `k` through `i-1`, respectively. The displayed inverse is
verified by finite arithmetic.

At `k = i`, this permutation is the identity. Moving from `k+1` to `k`
right-composes it with the adjacent transposition at `k,k+1`. At this stage the
left original label is `k` and the right original label is still `i`.
The hypothesis `R k i` therefore permits exactly this step. Decreasing
induction proves `P` at every such position, including zero.

A final pointwise calculation identifies `moveToPosition i 0` with the inverse
of Mathlib's `Fin.cycleRange i`. Thus the selected original occurrence moves
to the front while all other occurrences retain their relative order.
The proof uses only the given adjacent preservation rule and finite
permutation arithmetic; it supplies no commutation isomorphism for actual
representations.
