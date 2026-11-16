# Coset representatives with a prescribed last row

Module `Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerCosets`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`. These are helper lemmas for half (S) of the
Whittaker expansion (see `Interface`). They reduce a Whittaker term at level `j + 1` to a term at
level `j`: a coset `q ∈ N_(j+1)(F) \ GL_(j+1)(F)` is determined by the last row `ξ` of its
representative and by a coset of `N_j(F) \ GL_j(F)`, and `q` factors through an explicit matrix
`γ_ξ` whose height is controlled by the size and denominator of `ξ`. Here `d = [F : ℚ]` and
`‖·‖` on `F` is the sup norm of `mixedEmbedding F x`.

## Section `RowMatrix` (any field `K`, size `k + 1`)

* `rowMatrix ξ i`: the matrix whose last row is `ξ` and whose row `a ≠ last` is the standard
  basis row `e_(σ a)`, where `σ` is the transposition `(i last)` (`Equiv.swap i (Fin.last k)`).
* `rowMatrixInv ξ i`: the explicit inverse when `ξ_i ≠ 0`. Its row `b ≠ i` is `e_(σ b)`; its
  row `i` has entry `ξ_i⁻¹` in the last column and `-ξ_(σ a) ξ_i⁻¹` in column `a ≠ last`.
* `swap_last_eq_iff`: `σ a = i` exactly when `a` is the last index.
* `rowMatrix_mul_rowMatrixInv`: `rowMatrix ξ i * rowMatrixInv ξ i = 1` when `ξ_i ≠ 0`.
  Proof by direct computation of each entry. For a row `a ≠ last` only the term `b = σ a`
  contributes, which gives the identity row. For the last row and the last column only `b = i`
  contributes (`ξ_i ξ_i⁻¹ = 1`). For the last row and a column `c ≠ last`, the terms `b = i`
  and `b = σ c` contribute `-ξ_i ξ_(σ c) ξ_i⁻¹ + ξ_(σ c) = 0`.
* `rowGL ξ i hi`: `rowMatrix ξ i` as an element of `GL_(k+1)(K)` with inverse `rowMatrixInv ξ i`
  (a one-sided inverse of a square matrix is two-sided, `mul_eq_one_comm`). `coe_rowGL`,
  `coe_rowGL_inv` and `rowGL_last` (its last row is `ξ`) record the definitions.
* `rowPivot ξ`: an index with `ξ_i ≠ 0`, chosen by `Classical.choose` (and `0` for the zero
  row); `rowPivot_spec` is its defining property for `ξ ≠ 0`.
* `lastRow_ne_zero`: the last row of an invertible matrix is nonzero (otherwise the last
  diagonal entry of `g g⁻¹ = 1` would be `0`).
* `lastRow_mul_inv_eq`: if `g` and `h` have the same last row, then `g h⁻¹` has the last row of
  the identity, because the last row of `g h⁻¹` is (last row of `h`) times `h⁻¹`.

## Section `Cosets` (number field `F`)

* `cosetRow q`: the last row of the chosen representative `q.out`. It is nonzero
  (`cosetRow_ne_zero`).
* `cosetGamma q`: the matrix `γ_ξ = rowGL ξ (rowPivot ξ)` with `ξ = cosetRow q`. By
  `lastRow_mul_inv_eq`, `q.out γ_ξ⁻¹` has standard last row
  (`lastRowStandard_out_mul_cosetGamma_inv`).
* `cosetRestRep q`, `cosetRestRep_spec`: the Library lemma `exists_unitriangular_mul_padGL`
  writes a matrix with standard last row as `n diag(g', 1)` with `n` upper unitriangular; this
  chooses such `g'` and `n`.
* `cosetRest q`: the coset `N_j(F) g'`.
* `padGL_mem_rationalUpperUnipotent`: `u ↦ diag(u, 1)` maps `N_j(F)` into `N_(j+1)(F)`
  (Library `isUnitriangular_padGL`).
* `rightRel_cosetRest` (decomposition): `q.out ∈ N_(j+1)(F) diag((cosetRest q).out, 1) γ_ξ`.
  Proof: `(cosetRest q).out` and `g'` differ on the left by some `u ∈ N_j(F)`, so
  `q.out (diag((cosetRest q).out, 1) γ_ξ)⁻¹ = n diag(u, 1)`, which lies in `N_(j+1)(F)`.
* `cosetRow_cosetRest_injective` (injectivity): `q ↦ (cosetRow q, cosetRest q)` is injective.
  Equal last rows give equal `γ_ξ`, so both representatives lie in the same coset
  `N_(j+1)(F) diag(g'', 1) γ_ξ` by the decomposition.

## Section `Whittaker`

* `whittaker_padRational_coset`: for `j < r`, a standard additive character `ψ` and a function
  `f` on `GL_(r+1)(𝔸)` invariant on the left under rational points,
  `W_f(diag(q.out, I) y) = W_f(diag((cosetRest q).out, I) (diag(γ_ξ, I) y))`. This follows from
  the decomposition, the Library lemma `whittaker_padRational_of_rightRel` (a Whittaker value
  depends only on the coset), and the compatibility of the embeddings `padRational` and `padGL`
  (`padRational_mul`, `padRational_padGL`).

## Section `Heights`

* `norm_mixedEmbedding_natCast_mul_le`: `‖M x‖ ≤ M ‖x‖` for a natural number `M`.
* `exists_heightLE_rowGL` (height of `γ_ξ`): let `M` be a positive integer, `v ∈ 𝒪_F^(k+1)`
  with `M ξ = v`, every `‖v_b‖ ≤ N` for some `N ≥ 1`, and `ξ_i ≠ 0`. Then there is a positive
  integer `e ≤ M N^d` such that `rowGL ξ i` has height at most `(M N^d, e)` in the sense of
  `HeightLE` (from `WhittakerHeights`): every entry of the matrix and of its inverse has size at
  most `M N^d`, and becomes integral after multiplication by `e`. Proof: take
  `E = |N_{F/ℚ}(v_i)| ≤ N^d` with `E v_i⁻¹` integral and `‖v_i⁻¹‖ ≤ N^(d-1)`
  (`exists_nat_inv_integral`, `norm_mixedEmbedding_inv_le` from `WhittakerFrequency`; `v_i ≠ 0`
  because `ξ_i ≠ 0`), and `e = M E`. The entries of `rowMatrix ξ i` are `0`, `1` and
  `ξ_b = v_b / M`; those of the inverse are `0`, `1`, `ξ_i⁻¹ = M v_i⁻¹` and
  `-ξ_c ξ_i⁻¹ = -v_c v_i⁻¹`. Each bound and each integrality statement is checked directly.

All constructions are elementary linear algebra; the formulation (explicit inverse, the
particular representative `γ_ξ`, the height exponents) is this project's own, chosen for the
inductive majorant estimate of half (S).
