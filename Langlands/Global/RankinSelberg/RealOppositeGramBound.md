# Tail Gram determinants control the real opposite-cell coordinates

For a real matrix `x` of size `n`, `GramFormula.gram k x` is the Gram determinant of the rows
`k, …, n-1` of `x` (the determinant of `x xᵀ` on those rows, padded by the identity). This
module studies it on the transposes `uᵀ` of upper unipotent matrices `u`, which are lower
unitriangular.

* `one_le_gram_transpose`: `1 ≤ gram k uᵀ` for every `k` (the Library's `one_le_gram_of_lower`).
* `one_add_sq_entry_le_gram`: for `j < i`, `1 + |u_{j i}|² ≤ gram i uᵀ`.
* `oppositeGramProduct u` is the product `Π_{i<n} gram i uᵀ`, and
  `one_le_oppositeGramProduct` gives `1 ≤ oppositeGramProduct u`.

`RealOppositeGramBoundStatement`: for every `n` and every upper unipotent `u`,

`1 + ‖u - 1‖² ≤ oppositeGramProduct u`,

with the entrywise supremum norm. `realOppositeGramBound` proves it.

## Proof

By the Library's `gram_eq_of_lower`, for a lower unitriangular `L` the tail Gram determinant
`gram i L` equals `det(1 + A Aᵀ)`, where `A` is the lower-left block of a factor
`splitFactor i L` obtained by clearing the rows `≥ i` with a block lower triangular matrix of
determinant one. The row `i` of that factor coincides with the row `i` of `L`
(`splitFactor_row`), so the entry `A_{i j}` is `u_{j i}`. For any real square matrix `A` and
entry `(i, j)` one has `1 + A_{i j}² ≤ det(1 + A Aᵀ)`: split `1 + A Aᵀ` as
`(1 + c cᵀ) + Cᵀ C` with `c` the `j`-th column of `A`, use that adding a positive
semidefinite term `Cᵀ C` to a positive definite matrix does not decrease the determinant
(`det_le_det_add_transpose_mul_self`), and the rank-one determinant formula
`det(1 + c cᵀ) = 1 + c·c ≥ 1 + A_{i j}²`. Since every factor of the product is at least one,
each such factor is bounded by the product; the diagonal and the entries below it of `u - 1`
vanish. Taking the maximum over entries gives the bound.

The bound is used for the integrability of moments on the opposite cell in
`RealOppositeMoment` and for the peak argument in `RealOppositeNonzero`. It is an
internal, elementary inequality on the Iwasawa decomposition of lower unitriangular real
matrices.
