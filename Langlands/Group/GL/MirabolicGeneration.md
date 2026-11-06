# Generation by the mirabolic and its inverse-transpose image

This internal algebraic supporting unit is derived from the existing matrix
definitions and Mathlib's diagonal/transvection induction. It is intended for
the group stability step in the supercuspidal local converse argument.

The existing `mirabolic n F` is the subgroup of `GL_(n+1)(F)` whose last row is
the last standard row vector. The new `oppositeMirabolic n F` fixes the last
standard column vector: its last column is that vector. This definition and
`mirabolic_map_inverseTranspose` work over any commutative ring. The latter
identifies the opposite mirabolic with the image of the mirabolic under
`g ↦ (g⁻¹)ᵀ`. The membership equivalence uses closure of the mirabolic under
inversion.

Over any field, `eq_top_of_mirabolic_le_of_oppositeMirabolic_le` states that a
subgroup containing both groups is all of `GL_(n+1)` if `0 < n`. Every elementary
transvection belongs to one of these two subgroups: when its changed row is not
the last row it is in the mirabolic, and otherwise its changed column is not
the last column and it is in the opposite mirabolic.

For an invertible diagonal matrix with final entry `d ≠ 0`, choose a coordinate
`a` different from the final coordinate `l`. The product

`b = (I + E_la) (I + (d − 1) E_al) (I − d⁻¹ E_la)`

has last row `d e_l`. This is checked with the elementary row and column update
identities for transvections, separating the column `a` from the other columns.
Consequently `g b⁻¹` has last row `e_l`, so it is mirabolic. All three factors of
`b` and `g b⁻¹` belong to the proposed subgroup, proving that the invertible
diagonal matrix `g` does too. Mathlib's
`Matrix.diagonal_transvection_induction_of_det_ne_zero` now proves membership of
every invertible matrix.

`eq_top_of_mirabolic_le_of_inverseTranspose_mem` gives the subgroup criterion
directly from inclusion of the mirabolic and membership of each
inverse-transposed mirabolic element. `mirabolic_sup_inverseTranspose_eq_top`
expresses the same generation result as the supremum of these two subgroups,
in rank `n+2`. No topology, local field structure, representation theoretic
converse, or completeness hypothesis is used. This supporting unit does not
prove the supercuspidal local converse theorem.

Worker 1718 supplied the three-transvection last-row factorization and the
suggestion to use Mathlib matrix elimination. Worker 1648 implemented the
subgroups, comparisons, and generation proof.
