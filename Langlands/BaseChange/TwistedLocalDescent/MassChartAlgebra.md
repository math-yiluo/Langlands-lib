# Group-theoretic form of the twisted chart

Module `Langlands.BaseChange.TwistedLocalDescent.MassChartAlgebra`.

- `add_mem_lowerLevel`, `neg_mem_lowerLevel`, `zero_mem_lowerLevel`, `one_mem_lowerLevel_zero`,
  `mem_lowerLevel_zero_of_le`, `pow_mem_lowerLevel_zero`, `lowerInverse_mem_lowerLevel_zero`:
  block lower triangularity of `(1 + Z)⁻¹` for strictly block lower `Z`.
- `eq_zero_of_blockTriangular_of_mem_lowerLevel`: a block upper triangular and strictly block
  lower matrix is zero.
- `lowerUnit_eq_of_mul_inv_mem` (**`Ū ∩ P = 1`**): if `(1 + Z')(1 + Z)⁻¹ ∈ P` for strictly block
  lower `Z, Z'`, then `Z' = Z`; indeed `(1 + Z')(1 + Z)⁻¹ − 1 = (Z' − Z)(1 + Z)⁻¹` is strictly block
  lower and block upper triangular.

For a nontrivially normed field `𝕂` and a ring endomorphism `σ` of `𝕂`:

- `mul_one_add_twistedChart`: for `d dinv = 1`,
  `d (1 + χ(X)) = (1 + X_𝔲̄)⁻¹ d (1 + X_𝔭) σ(1 + X_𝔲̄)` with `χ = twistedChart B σ d dinv`.
- `val_twistedConj_lowerUnit`: the matrix of `(1 + Z)⁻¹ d h σ(1 + Z)`.
- `exists_twistedConj_of_mem_chart` (for `𝕂` ultrametric, proper and nontrivially normed): if
  `y ∈ GL_n` has matrix `d (1 + χ(X))` with `‖X‖ ≤ r` and `U` is a congruence subgroup of radius
  `r`, then `y = (1 + Z)⁻¹ d h σ(1 + Z)` with `Z = X_𝔲̄`,
  `‖Z‖ ≤ r`, and `h ∈ P ∩ U` the element with matrix `1 + X_𝔭`.
