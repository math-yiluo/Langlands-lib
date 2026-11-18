# Labelled permutations that reverse consecutive blocks

`MonomialPattern n α` consists of a permutation of the `n` positions with a label of type `α` at each position. Whenever a pair of positions and its image are both increasing, the pair is adjacent precisely when its image is adjacent. Adjacent ascents must have equal labels. This is an internal combinatorial model for the root compatibility conditions on upper-unipotent double cosets.

For a pattern in positive rank, both the permutation and its inverse can rise by at most one at each adjacent step. Let `p` be the position of the greatest value. Iterating the two bounds gives `w(i) + p = n + i` for positions `i ≤ p` in rank `n+1`. The initial block is therefore sent in order to the greatest values, and has one constant label. The remaining positions map to the smaller values and have the same pattern property after shifting their positions down. Conversely, an initial block with a chosen label and any smaller pattern determine a larger pattern. Increasing pairs cannot cross between the two blocks.

`firstBlockEquiv` implements this splitting, indexed by the size of the remaining block. In the finite case the rank-zero count is one. The equivalence expresses each positive-rank count as the label count times the sum over the smaller ranks. Comparing successive sums gives the factor `Nat.card α + 1` at each recursion step.
