# The limit argument along the maximal parabolic subgroup `P_{m,1}`

Lean module: `Langlands.Representation.Archimedean.JacquetLimit`.

This module proves the asymptotic step of the Langlands-lemma argument along
`P_{m,1} ⊂ GL_{m+1}(ℝ)` (`integral_mul_jacquetStep_eq_zero`). Let `u` be in the principal
series of `χ⁻¹` and `h` in that of `χ`, with `χ` a strictly dominant signed power (module
`PartialJacquetIntegral`). If `∫_{O(m+1)} u(κ g) h(κ) dκ = 0` for every `g ∈ GL_{m+1}(ℝ)`, then

`∫_{O(m)} u(ι(k)) · T h(k) dk = 0`,

where `T` is the partial Jacquet integral and `ι(k) = diag(k, 1)`. Integrals over `O(n)` use
the Library's normalized Haar measure `RealPrincipalSeriesDuality.haarK n`.

Declarations without a prefix are in the namespace `Langlands.Archimedean.JacquetLimit`.

## Auxiliary results

* `principalSeriesCharacter_dual_mul`: the characters of `χ⁻¹` and of `χ` multiply to the
  modulus character (`MaximalParabolicIntegration.modulusCharacter`).
  `norm_modulusCharacter` computes the absolute value of the modulus character.
* `norm_le_of_covariant`: a modulus-covariant `F` with `‖F‖ ≤ C` on `O(m+1)` satisfies
  `‖F(J(x,1)κ)‖ ≤ C ∏_l (1 + x_l²)^{−1}`. This is `ParabolicChartBound.norm_le_chart` with all
  chart exponents equal to `−1`.
* `iotaGL_mul_chartGL`: `ι(k) J(v,1) = J(v k⁻¹, 1) ι(k)`. `chartGL_zero`: `J(0,1) = 1`.
  `iotaGL_mul_dlastGL`: `ι(k)` commutes with `d(s) = diag(1, …, 1, s)`.
  `apply_dlastGL_mul`: `u(d(s) y)` equals the character value at `(1, …, 1, s)` times `u(y)`.

## The integration formula with the compact variable outside

`integral_eq_chart'`: for `F` smooth and modulus-covariant,

`∫_{O(m+1)} F = c_m ∫_{O(m)} ∫_{ℝ^m} F(J(x,1) ι(k)) dx dk`.

Proof. Start from the accepted `MaximalParabolicIntegration.integral_eq_chart`, which has the
form `c_m ∫_v ∫_k F(ι(k) J(v,1))`. Exchange the integrals with `integral_integral_swap`.
Integrability on `O(m) × ℝ^m` comes from `integrable_prod_iff`: for each `k`, the function
`F(ι(k)J(v,1)) = F(J(v k⁻¹,1)ι(k))` is dominated by a rotated integrable function
(`integrable_comp_vecMul`), and its integral is bounded uniformly in `k`. Finally rotate
`x = v k⁻¹` (`integral_vecMul_eq`, with `|det k⁻¹| = 1`).

## The limit

`integral_mul_jacquetStep_eq_zero`. For `s > 0` put `d = d(s)` and `F(y) = u(y d) h(y)`. `F` is
smooth (`contMDiff_mul_fun`) and modulus-covariant. By the hypothesis and `integral_eq_chart'`,

`0 = c_m ∫_k ∫_x u(J(x,1) ι(k) d) h(J(x,1) ι(k)) dx dk`.

`J(x,1) ι(k) d = d J(s⁻¹x, 1) ι(k)`, and `u(d y)` is a nonzero character value times `u(y)`.
Since `c_m > 0`, this gives `I(s) = 0`, where

`I(s) = ∫_k ∫_x u(J(s⁻¹x,1) ι(k)) h(J(x,1) ι(k)) dx dk`.

Let `s = N + 1 → ∞`. The chart bounds `PartialJacquet.norm_le_partialSq` for `u` (exponents
`chartExponent (−e)`) and for `h` (exponents `chartExponent e`) have exponents with sum `−1`.
By `ParabolicChartBound.prod_rpow_mul_prod_rpow_le` with `|s⁻¹| ≤ 1`, the integrand is dominated,
uniformly in `s ≥ 1` and `k`, by `C_u C_h ∏ (1 + x_l²)^{max(chartExponent e l, −1)}`. That bound
is integrable because every exponent is `< −1/2`. Dominated convergence
(`tendsto_integral_of_dominated_convergence`), first in `x` for each `k` and then in `k` with a
constant bound, gives
`I(N + 1) → ∫_k u(ι(k)) ∫_x h(J(x,1)ι(k)) dx dk = ∫_k u(ι(k)) T h(k) dk`.
The pointwise limit uses `J(s⁻¹x,1) → J(0,1) = 1`. Since every `I(N + 1) = 0`, the limit is `0`.
