# Endpoint bounds in a leading unequal-rank block

This is an internal consequence of the actual matrix in
Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg convolutions* (1983),
Section 4.10(2), printed page 419 (registered source
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`).
The source does not separately state this auxiliary endpoint formulation.
The proof combines the existing coefficient root bound with a determinant
calculation, and then specializes the existing actual diagonal factorization.

The algebraic lemma `unequalRankMatrix_last_entry_minor` is valid over any
field. Write `R = n + (j + k + 1)`. In `unequalRankMatrix j k g x`, take the
principal suffix whose first index has numerical value `n`, the last index of
the leading rank `n + 1` block. This square submatrix is lower triangular:
its first diagonal entry is `g (Fin.last n) (Fin.last n)` and every other
diagonal entry is one. Its determinant is therefore exactly that entry.
This calculation allows arbitrary `g`, arbitrary rectangle `x`, and zero
complementary dimensions.

For any p-adic field with its canonical topology and valuation,
`iwasawa_principal_suffix_minor_bound` bounds the normalized absolute value
of each principal suffix minor of `u * diagonalUnits a * κ` by the product
of the absolute values of the corresponding diagonal units. Here `u` is
upper unipotent and `κ` belongs to the actual integral subgroup, which
requires integrality of both the matrix and its inverse. Restricting an
upper triangular matrix product to suffix rows factors its determinant.
The diagonal entries of the upper unipotent factor are one, and the
remaining determinant belongs to the integer subring.

`unequalRankMatrix_last_entry_bound` assumes a decomposition of the actual
unequal-rank matrix with adjacent diagonal ratios bounded by a real
`B ≥ 1`. Its terminal row is the last standard basis row. The existing
`diagonal_abs_last` and `diagonal_abs_bound` then bound every diagonal
absolute value by `B ^ R`. The suffix has at most `R + 1` indices, so the
minor bound gives
`|g (Fin.last n) (Fin.last n)| ≤ (B ^ R) ^ (R + 1)`.
This is a coarse bound, sufficient for an endpoint estimate.

`IsBlockSumLastEntryBound` says that a real bound is at least one and
controls this leading endpoint entry whenever the supplied coefficient
is nonzero at
`blockSum (unequalRankMatrix j k g x, D) * c`.
It quantifies over all leading matrices, rectangles, complementary
invertible blocks of rank `d + 1`, and right factors in the integral
subgroup. `exists_blockSum_last_entry_bound` proves the property for every
smooth complex representation and every coefficient in the model of any
supplied Whittaker functional. Field and representation universes are
independent. No irreducibility or nonzero-functional premise is used.
The proof chooses a uniform natural root bound `L` before all these
variables and applies the preceding inequality with `B = q ^ L`, where
`q` is the residue cardinality.

`exists_reindex_blockSum_last_entry_bound` transports this result along
equality of the actual ranks, without changing the coefficient. Finally,
`IsLeviSecondEndpointBound` states that a bound at least one controls
`|b 1 (Fin.last (m 1)) (Fin.last (m 1))|` whenever the coefficient is nonzero
at `matrix h hr (leviEmbedding b * c) x y`. The block sizes are arbitrary
positive successor ranks with total `t + 1`, `j,k` are arbitrary natural
numbers, and `r = t + (j + k + 1)`. Both actual Levi blocks and both
rectangles are universally quantified.

`exists_levi_second_endpoint_bound` applies the block-sum bound to the
exact factorization `matrix_levi_diagonalBlocks`. The leading block is
`unequalRankMatrix j 0 (b 1) (y.rev * (b 1).val)`, the trailing block is
`trailingBlock (b 0) x.rev`, and the right integral factor is the fixed
column permutation multiplied by `append hr c`. Their integrality is
already proved by the support module. This establishes a uniform bound
for the original second block's endpoint entry. Propagation to an
opposite cone, rectangle volumes, convergence and the Laurent identity
remain separate obligations.
