# Growth of principal-series functions along the opposite unipotent radical of `P_{m,1}`

Lean module: `Langlands.Representation.Archimedean.ParabolicChartBound`.

This module bounds a function `F` on `GL_{m+1}(ℝ)` that transforms on the left under the upper
triangular Borel subgroup by a character of known absolute value. The bound holds at the points
`J(x,1) κ`, where `J(x,1)` (`MaximalParabolicIntegration.chartGL x`) is the identity matrix with
last row `(x, 1)` and `κ ∈ O(m+1)`. The statement is
`Langlands.Archimedean.ParabolicChartBoundStatement`, proved as
`Langlands.Archimedean.parabolicChartBound`.

The module also provides the integrable dominating functions used later for the partial Jacquet
integral and the limit argument along `P_{m,1}` (modules `PartialJacquetIntegral` and
`JacquetLimit`, Task 6749).

Notation. Indices run over `Fin (m+1) = {0, …, m}`. `O(m+1)` is `unitaryCompact ℝ (m+1)`.
Declarations without a prefix are in the namespace
`Langlands.Archimedean.ParabolicChartBound`.

## The statement

`ParabolicChartBoundStatement`. Let `F : GL_{m+1}(ℝ) → ℂ`, `c : (ℝˣ)^{m+1} → ℂ` and `σ : ℕ → ℝ`
satisfy:

* `F(diag(a) u g) = c(a) F(g)` for every `a ∈ (ℝˣ)^{m+1}`, every upper unipotent `u` and every `g`;
* `‖c(a)‖ = ∏_l |a_l|^{σ_l}`;
* `‖F(k)‖ ≤ C` for `k ∈ O(m+1)`.

Then for every `x ∈ ℝ^m` and `κ ∈ O(m+1)`,

`‖F(J(x,1) κ)‖ ≤ C ∏_{l=0}^{m-1} (1 + ∑_{j ≤ l} x_j²)^{(σ_{l+1} − σ_l)/2}`.

In Lean, the inner sum is `∑ j : Fin m, if (j : ℕ) < l + 1 then x j ^ 2 else 0`.

Provenance. Derived, internal infrastructure. This is the standard way of estimating
principal-series functions on the opposite unipotent radical through the Iwasawa decomposition
and Gram determinants.

## Definitions

* `partialSq x l = r_l(x) = 1 + ∑_{j < l} x_j²`.
* `tailVec l x`: the entries `x_j` with `j ≥ l`, and `0` at the other positions.

## Proof

1. **Gram determinants of the chart** (`gram_chart`). For `l ≤ m`, the Gram determinant of the
   rows `l, …, m` of `J(x,1)` is `r_l(x)` (`GramFormula.gram`). The padded Gram matrix factors as
   `Jmat(c, 1) · Jmat(c, r_l(x))ᵀ` with `c = tailVec l x` (`paddedGram_chart`). This is checked
   entrywise, splitting `Fin (m+1)` into its first `m` indices and its last index. Both factors
   are lower triangular, with determinants `1` and `r_l(x)` (`MaximalParabolicIntegration.det_Jmat`).
2. **Invariances.** Gram determinants do not change under right multiplication by an orthogonal
   matrix (`gram_mul_orthogonal`). For `b = diag(a) u` with `u` upper unipotent,
   `gram l (b κ) = (∏_{j ≥ l} a_j)²` (`gram_diagonal_mul`, from `GramFormula.gram_mul`).
3. **Diagonal of the Iwasawa factor** (`prod_tail_sq_eq`). Write `J(x,1) κ = diag(a) u k` with
   `k ∈ O(m+1)`, using the Library's `exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact`.
   Steps 1 and 2 give `(∏_{j ≥ l} a_j)² = r_l(x)` for every `l ≤ m`.
4. **Summation by parts** (`sum_mul_eq_sum_sub`). Put `T_l = ∑_{j ≥ l} log|a_j|`. Then
   `T_0 = 0` (since `r_0 = 1`) and `T_{m+1} = 0`, so
   `∑_l σ_l log|a_l| = ∑_{l<m} (σ_{l+1} − σ_l) T_{l+1}`.
5. **Conclusion** (`norm_le_chart`). `‖F(J(x,1)κ)‖ = ‖c(a)‖ ‖F(k)‖ ≤ C ∏ |a_l|^{σ_l}`. Steps 3
   and 4, after exponentiating, turn `∏ |a_l|^{σ_l}` into `∏_{l<m} r_{l+1}(x)^{(σ_{l+1}−σ_l)/2}`.

## Dominating functions

* `integrable_one_add_sq_rpow`: `t ↦ (1 + t²)^γ` is integrable on `ℝ` for `γ < −1/2`. This
  comes from Mathlib's `integrable_rpow_neg_one_add_norm_sq`.
* `integrable_prod_one_add_sq_rpow`: `x ↦ ∏_l (1 + x_l²)^{γ_l}` is integrable on `ℝ^m` if
  every `γ_l < −1/2` (`Integrable.fintype_prod`).
* `prod_partialSq_rpow_le`: if every `ε_l ≤ 0`, then
  `∏ r_{l+1}(x)^{ε_l} ≤ ∏ (1 + x_l²)^{ε_l}`. This holds because `r_{l+1}(x) ≥ 1 + x_l²`
  (`one_add_sq_le_partialSq`).
* `prod_rpow_mul_prod_rpow_le`: let `|s| ≤ 1`, `ε^u_l + ε^h_l = −1` and `ε^h_l < 0`. Then
  `∏ r_{l+1}(s x)^{ε^u_l} · ∏ r_{l+1}(x)^{ε^h_l} ≤ ∏ (1 + x_l²)^{max(ε^h_l, −1)}`. The proof
  splits into the cases `ε^u_l ≥ 0` and `ε^u_l < 0`, and uses
  `1 ≤ r_l(s x) ≤ r_l(x)` (`partialSq_smul_le`).
