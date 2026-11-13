# The exterior square of a `4 × 4` matrix

Module `Langlands.GroupScheme.ExteriorSquareMatrix`, namespace
`Langlands.GroupScheme.ExteriorSquare`. Internal linear algebra over an arbitrary commutative ring
`A`, with no characteristic assumption.

## Definitions

* `pair : Fin 6 → Fin 4 × Fin 4` lists the increasing pairs
  `(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)`, the index set of the basis
  `e₀∧e₁, e₀∧e₂, e₀∧e₃, e₁∧e₂, e₁∧e₃, e₂∧e₃` of `Λ² A⁴`.
* `matrix M` for `M : Matrix (Fin 4) (Fin 4) A` is the `6 × 6` matrix of `2 × 2` minors,
  `matrix M I J = M i k * M j l - M i l * M j k` for `pair I = (i, j)`, `pair J = (k, l)`. It is
  the matrix of `Λ² M` in the basis above.
* `pfaffian` is the symmetric `6 × 6` matrix with entries `1` at
  `(e₀∧e₁, e₂∧e₃)`, `-1` at `(e₀∧e₂, e₁∧e₃)`, `1` at `(e₀∧e₃, e₁∧e₂)` and their transposes, and `0`
  elsewhere: the Gram matrix of the symmetric bilinear wedge pairing
  `(ξ, η) ↦ ξ ∧ η ∈ Λ⁴ A⁴ = A`. The module treats only this bilinear pairing. The split Pfaffian
  quadratic form `q = x₀₁ x₂₃ - x₀₂ x₁₃ + x₀₃ x₁₂` has `ξ ∧ ξ = 2 q(ξ)`, so in characteristic two
  `ξ ∧ ξ = 0` and the identities below do not show that `q` is preserved.

## Results

* `matrix_mul`: `matrix (M * N) = matrix M * matrix N` (Cauchy–Binet for `2 × 2` minors);
  `matrix_one`: `matrix 1 = 1`.
* `matrix_transpose`: `matrix Mᵀ = (matrix M)ᵀ`; `matrix_map`: `matrix` commutes with applying a
  ring homomorphism entrywise.
* `pfaffian_mul_self`: `pfaffian * pfaffian = 1`; `pfaffian_transpose`: `pfaffianᵀ = pfaffian`.
* `det_fin_four`: the cofactor expansion of a `4 × 4` determinant along the first row.
* `transpose_mul_pfaffian_mul`: `(matrix M)ᵀ * pfaffian * matrix M = det M • pfaffian`, and
  `mul_pfaffian_mul_transpose`: `matrix M * pfaffian * (matrix M)ᵀ = det M • pfaffian` (from the
  first applied to `Mᵀ`).

All identities are polynomial identities in the entries; the proofs expand all entries and use
`ring`.
