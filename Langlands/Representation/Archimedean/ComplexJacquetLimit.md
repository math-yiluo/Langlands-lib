# The limit argument along the maximal parabolic subgroup `P_{m,1}` of `GL_{m+1}(ℂ)`

Lean module: `Langlands.Representation.Archimedean.ComplexJacquetLimit`.

This module is infrastructure for the proof of
`ComplexStandardLanglandsQuotientStatement`. It is the complex counterpart of the module
`JacquetLimit` for `GL_n(ℝ)`, and follows its proof.

The module proves the asymptotic step of the Langlands-lemma argument along
`P_{m,1} ⊂ GL_{m+1}(ℂ)` (`ComplexJacquetLimit.integral_mul_jacquetStep_eq_zero`). Let `u` be in
the principal series of `χ⁻¹` and `h` in that of `χ`, with `χ` a strictly dominant phase power
(module `ComplexPartialJacquet`). If `∫_{U(m+1)} u(κ g) h(κ) dκ = 0` for every
`g ∈ GL_{m+1}(ℂ)`, then

`∫_{U(m)} u(ι(k)) · T h(k) dk = 0`,

where `T h(g) = ∫_{ℂ^m} h(J(x,1) ι(g)) dx` is the partial Jacquet integral, `J(x,1)` the identity
matrix with last row `(x, 1)` and `ι(k) = diag(k, 1)`. Integrals over `U(n)` use the Library's
Haar probability measure `ComplexDuality.unitaryHaar n`. The main statement is
`Langlands.Archimedean.ComplexJacquetLimitStatement`, proved as
`Langlands.Archimedean.complexJacquetLimit`.

Notation: `GL_n(ℂ)` is `Langlands.GeneralLinear n ℂ`, `U(n)` is `unitaryCompact ℂ n`.
`chartGL`, `iotaGL`, `dlastGL` (`d(s) = diag(1, …, 1, s)`), `natural`, `integral_eq_chart`,
`chartConstant` and `normSqC_det_unitary` come from `ComplexMaximalParabolicIntegration`;
`modulusCharacter n` (the characters `(|z|²)^{(n−1)/2 − l}`, whose principal series is that of the
modulus character of the Borel subgroup) from `ComplexKIntegralInvariance`; `partialSq`,
`integrable_prod_one_add_sq_rpow`, `prod_partialSq_rpow_le` and `prod_rpow_mul_prod_rpow_le` from
`ComplexParabolicChartBound`; `IsPhasePower`, `dualChar`, `IsStrictlyDominant`, `chartExponent`,
`norm_le_partialSq`, `integral_vecMul_eq` and `jacquetStep` from `ComplexPartialJacquet`.
Declarations without a prefix are in the namespace `Langlands.Archimedean.ComplexJacquetLimit`.

## The statement

`ComplexJacquetLimitStatement`: let `χ_l : ℂˣ → ℂ` and `e : ℕ → ℂ` satisfy
`χ_l(z) = χ_l(z/|z|) (|z|²)^{e_l}`, `χ_l(1) = 1`, `|χ_l(z/|z|)| = 1`, and `Re e_{l+1} < Re e_l`
for `l < m`. Let `u` be in `principalSeries ℂ (m+1)` of the characters `z ↦ χ_l(z)⁻¹` and `h` in
`principalSeries ℂ (m+1) χ`. If `∫_{U(m+1)} u(κ g) h(κ) dκ = 0` for every `g`, then
`∫_{U(m)} u(ι(k)) (∫_{ℂ^m} h(J(x,1) ι(k)) dx) dk = 0`.

Provenance. Derived, internal infrastructure: the asymptotic step of the Langlands lemma
(leading term of a matrix coefficient along `A_P^+` given by the Jacquet integral), made explicit
for `P_{m,1}` through the integration formula of `ComplexMaximalParabolicIntegration`. No
literature claim beyond this standard argument.

## Auxiliary results

* `contMDiff_mul_fun`: products of smooth functions on `GL_n(ℂ)` are smooth (through the Library's
  `unitsExtension`, `contDiffOn_unitsExtension` and `contMDiff_of_contDiffOn`).
* `isPhasePower_modulus`: `modulusCharacter n` is a phase power with exponents
  `(n−1)/2 − l`.
* `principalSeriesCharacter_dual_mul`: the principal-series characters of `χ⁻¹` and of `χ`
  multiply to that of `modulusCharacter N`.
* `norm_le_of_modulus`: `F` in the principal series of `modulusCharacter (m+1)` with `|F| ≤ C` on
  `U(m+1)` satisfies `|F(J(x,1)κ)| ≤ C ∏_l (1 + |x_l|²)^{−2}` for `κ ∈ U(m+1)`. This is
  `norm_le_partialSq` with all chart exponents equal to `−2`, followed by
  `prod_partialSq_rpow_le`.
* `iotaGL_mul_chartGL`: `ι(k) J(v,1) = J(v k⁻¹, 1) ι(k)`. `chartGL_zero`: `J(0,1) = 1`.
  `iotaGL_mul_dlastGL`: `ι(k)` commutes with `d(s)`. `apply_dlastGL_mul`: `u(d(s) y)` equals the
  principal-series character at `(1, …, 1, s)` times `u(y)`. `norm_det_inv_sq`:
  `|det k⁻¹|² = 1` for `k ∈ U(m)`.

## The integration formula with the compact variable outside

`integral_eq_chart'`: for `F` in the principal series of `modulusCharacter (m+1)`,

`∫_{U(m+1)} F = c_m ∫_{U(m)} ∫_{ℂ^m} F(J(x,1) ι(k)) dx dk`.

Proof. Start from `ComplexMaximalParabolicIntegration.integral_eq_chart`, which has the form
`c_m ∫_v ∫_k F(ι(k) J(v,1))` (the inner integral is `natural F (J(v,1))`). Exchange the integrals
with `integral_integral_swap`. Integrability on `U(m) × ℂ^m` comes from `integrable_prod_iff`: for
each `k`, `F(ι(k) J(v,1)) = F(J(v k⁻¹,1) ι(k))` is dominated by the integrable function
`C ∏ (1 + |·_l|²)^{−2}` composed with `v ↦ v k⁻¹` (`integrable_comp_vecMul`), and its integral is
bounded uniformly in `k` (`integral_vecMul_smul` with `|det k⁻¹|² = 1`). Finally substitute
`x = v k⁻¹` (`integral_vecMul_eq`).

## The limit

`integral_mul_jacquetStep_eq_zero`. For real `s > 0` put `d = d(s)` and `F(y) = u(y d) h(y)`.
`F` is smooth (`contMDiff_mul_fun`, with `rightTranslation_mem_principalSeries` for `y ↦ u(y d)`)
and lies in the principal series of `modulusCharacter (m+1)` by
`principalSeriesCharacter_dual_mul`. By the hypothesis and `integral_eq_chart'`,

`0 = c_m ∫_k ∫_x u(J(x,1) ι(k) d) h(J(x,1) ι(k)) dx dk`.

`J(x,1) ι(k) d = d J(s⁻¹x, 1) ι(k)` (`chartGL_mul_dlastGL`), and `u(d y)` is a nonzero character
value `c'` times `u(y)` (`apply_dlastGL_mul`; `c' ≠ 0` by `norm_principalSeriesCharacter`). Since
`c_m > 0` (`chartConstant_pos`), this gives `I(s) = 0`, where

`I(s) = ∫_k ∫_x u(J(s⁻¹x,1) ι(k)) h(J(x,1) ι(k)) dx dk`.

Let `s = N + 1 → ∞`. The chart bounds `norm_le_partialSq` for `u` (exponents
`chartExponent (−e)`) and for `h` (exponents `chartExponent e`) have exponents with sum `−2`, and
`chartExponent e l < 0`. By `prod_rpow_mul_prod_rpow_le` with `|s⁻¹| ≤ 1`, the integrand is
dominated, uniformly in `s ≥ 1` and `k`, by `C_u C_h ∏ (1 + |x_l|²)^{max(chartExponent e l, −2)}`.
That bound is integrable on `ℂ^m` because every exponent is `< −1`
(`chartExponent_lt`). Dominated convergence (`tendsto_integral_of_dominated_convergence`), first
in `x` for each `k` and then in `k` with a constant bound, gives
`I(N + 1) → ∫_k u(ι(k)) ∫_x h(J(x,1)ι(k)) dx dk = ∫_k u(ι(k)) T h(k) dk`.
The pointwise limit uses `J(s⁻¹x,1) → J(0,1) = 1` and continuity of `u`. Since every
`I(N + 1) = 0`, the limit is `0`.

`complexJacquetLimit` assembles the statement from `integral_mul_jacquetStep_eq_zero`.
