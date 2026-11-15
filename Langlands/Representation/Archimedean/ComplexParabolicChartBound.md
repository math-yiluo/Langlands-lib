# Growth of complex principal-series functions along the opposite unipotent radical of `P_{m,1}`

Lean module: `Langlands.Representation.Archimedean.ComplexParabolicChartBound`.

Worker 140 wrote this module for Task 7063 (`f2d2e257-dd4b-4820-96ab-faa9c832ffb8`), the proof of
`ComplexStandardLanglandsQuotientStatement`. It is the complex counterpart of Worker 5220's draft
module `ParabolicChartBound` for `GL_n(ℝ)` (Task 6749), and follows its proof.

The module bounds a function of a principal series of `GL_{m+1}(ℂ)` along the chart
`x ↦ J(x, 1)` of the opposite unipotent radical of the maximal parabolic subgroup `P_{m,1}`. It also
gives the integrability and domination estimates that the partial Jacquet integral and its limit
argument use. The main statement is `Langlands.Archimedean.ComplexParabolicChartBoundStatement`,
proved as `Langlands.Archimedean.complexParabolicChartBound`.

Notation: `GL_{m+1}(ℂ)` is `Langlands.GeneralLinear (m + 1) ℂ`, `U(m+1)` is `unitaryCompact ℂ (m+1)`.
`chartGL x` (`ComplexMaximalParabolicIntegration`) is the identity matrix with last row `(x, 1)`,
for `x ∈ ℂ^m`, and `Jmat r` the identity with last row `r`. `Iwasawa.diagonalUnits a` is `diag(a)`
and `upperUnipotent` the upper unipotent group. `paddedGram` and `gram` are the polarized Gram
matrices and determinants of `ComplexGramFormula` (rows `≥ l` of `x yᵀ`). Declarations without a
prefix are in the namespace `Langlands.Archimedean.ComplexParabolicChartBound`.

## The statement

`ComplexParabolicChartBoundStatement`: let `F : GL_{m+1}(ℂ) → ℂ`, `c : (ℂˣ)^{m+1} → ℂ` and
`σ : ℕ → ℝ` satisfy `F(diag(a) u g) = c(a) F(g)` for all `a`, upper unipotent `u` and `g`, and
`‖c(a)‖ = ∏_l |a_l|^{σ_l}`. If `‖F(k)‖ ≤ C` for all `k ∈ U(m+1)`, then for every `x ∈ ℂ^m` and
`κ ∈ U(m+1)`,

`‖F(J(x,1) κ)‖ ≤ C ∏_{l<m} r_{l+1}(x)^{(σ_{l+1} − σ_l)/2}`,
`r_l(x) = 1 + ∑_{j < l} |x_j|²`.

Provenance. Derived, internal infrastructure without a literature source. It is the standard
estimate of a principal-series function by the spherical function of its absolute character, made
explicit on the chart through Gram determinants of lower rows.

## Definitions

* `partialSq x l = 1 + ∑_{j<l} |x_j|²` (`r_l` above); it is `≥ 1`, and `≥ 1 + |x_l|²` at `l + 1`
  (`one_add_sq_le_partialSq`); it decreases under scaling by `|s| ≤ 1` (`partialSq_smul_le`).
* `tailVec l x`: the entries of `x` at positions `≥ l`, and `0` elsewhere.

## Proof

1. **Gram determinants of the chart** (`paddedGram_chart`, `gram_chart`). The polarized padded Gram
   matrix of `(J(x,1), J(x̄,1))` on the rows `≥ l` factors as
   `J(tail_l x, 1) · J(tail_l x̄, r_l(x))ᵀ`, so `gram l (J(x,1)) (J(x̄,1)) = r_l(x)`.
2. **Invariance and Iwasawa** (`paddedGram_mul_unitary`, `prod_tail_sq_eq`). Right multiplication of
   `(y, z)` by `(κ, κ̄)` with `κ` unitary does not change the polarized padded Gram matrix. If
   `J(x,1) κ = diag(a) u k` (Iwasawa, `k` unitary), comparing `gram l` of both sides with
   `ComplexGramFormula.gram_mul_conj` gives `|∏_{j≥l} a_j|² = r_l(x)` for `l ≤ m`.
3. **Summation by parts** (`sum_mul_eq_sum_sub`, `norm_le_chart`). With
   `T_l = ∑_{j≥l} log |a_j| = (log r_l(x))/2`, `T_0 = 0` and `T_{m+1} = 0`,
   `∑_l σ_l log |a_l| = ∑_{l<m} (σ_{l+1} − σ_l) T_{l+1}`. Hence
   `‖F(J(x,1) κ)‖ = ‖c(a)‖ ‖F(k)‖ = ∏_{l<m} r_{l+1}(x)^{(σ_{l+1}−σ_l)/2} ‖F(k)‖ ≤ C ∏ …`.
4. **Integrability** (`integrable_one_add_sq_rpow`, `integrable_prod_one_add_sq_rpow`). For `γ < −1`,
   `t ↦ (1 + |t|²)^γ` is integrable on `ℂ` (Mathlib's `integrable_rpow_neg_one_add_norm_sq`, real
   dimension `2`), and `x ↦ ∏_l (1 + |x_l|²)^{γ_l}` is integrable on `ℂ^m` when every `γ_l < −1`
   (`Integrable.fintype_prod`).
5. **Domination** (`prod_partialSq_rpow_le`, `prod_rpow_mul_prod_rpow_le`). For nonpositive exponents,
   `∏ r_{l+1}(x)^{ε_l} ≤ ∏ (1 + |x_l|²)^{ε_l}`. For a dual pair of exponents `ε^u_l + ε^h_l = −2` with
   `ε^h_l < 0` and `|s| ≤ 1`,
   `∏ r_{l+1}(s x)^{ε^u_l} · ∏ r_{l+1}(x)^{ε^h_l} ≤ ∏ (1 + |x_l|²)^{max(ε^h_l, −2)}`: if
   `ε^u_l ≥ 0` use `r_{l+1}(s x) ≤ r_{l+1}(x)`, otherwise `r_{l+1}(s x)^{ε^u_l} ≤ 1`.
