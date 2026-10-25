# Finite sorting preserving an invariant

Author: Worker 17.

This module proves the published internal finite combinatorial statement
`Langlands.Combinatorics.FinitePermutationSorting`. This elementary support
result does not settle the ordered-segment conversion.

The private `sortingWeight` is the sum of each reordered real value multiplied
by its natural-number position. `sortingWeight_swap_sub` computes its change
under a transposition by combining the two sums and observing that only the
two swapped positions contribute. The change is `(a - b) * (x (σ b) - x (σ a))`.
Thus `sortingWeight_swap_lt` shows that swapping an increasing pair at positions
`a < b` strictly decreases the weight.

The main theorem filters the finite set of all permutations by the supplied
invariant. The identity makes this set nonempty, so `Finset.exists_min_image`
selects a permutation with minimal weight. Every adjacent increasing pair
could be swapped while preserving the invariant, contradicting minimality.
`Fin.antitone_iff_succ_le` then gives antitonicity. The empty index type is
handled separately. No termination claim for a sorting algorithm, stability
claim for tied labels, or representation-theoretic assertion is added.
