# The limit argument for the regularized vector

Lean module: `Langlands.Representation.Archimedean.RealSphericalLimit`, namespace
`Langlands.Archimedean.RealSphericalLimit`. It imports `RealSphericalChart` and
`JacquetLimit`, and it is part of the proof of `RealSphericalCyclicStatement`.

Setting: `χ` is a signed power with exponents `e` and `χ_l(−1) = 1` for every `l`, on
`GL_{m+1}(ℝ)`, with `IsWeaklyDominant e m`. `H = signVector (m+1) e 0 (bump 0 m 1)` is the
regularized vector of the principal series of `χ`. `dualChar χ` is the dual character
`χ⁻¹` (Library), and `haarK n` is the normalized Haar measure on `O(n)`.

## Main result `integral_iota_eq_zero`

Let `u` be in the principal series of `dualChar χ` on `GL_{m+1}(ℝ)` with
`∫_{O(m+1)} u(κ g) H(κ) dκ = 0` for every `g`. Then `∫_{O(m)} u(ι(k)) dk = 0`, where
`ι(k) = diag(k, 1)`.

The proof follows the Library's `JacquetLimit.integral_mul_jacquetStep_eq_zero` with `h = H`.
That lemma assumes strictly dominant exponents, so its domination step is redone here.

1. **Pairing identity.** Fix `s > 0` and put `F(y) = u(y · dlast(s)) H(y)`, with
   `dlast(s) = diag(1, …, 1, s)`. `F` is smooth and modulus-covariant, because the characters of
   `u` and `H` multiply to the modulus character (`principalSeriesCharacter_dual_mul`). The
   Library's `JacquetLimit.integral_eq_chart'` rewrites `∫_{O(m+1)} F`, which is `0` by
   hypothesis, as `chartConstant m` times the chart integral
   `∫_{O(m)} ∫_{ℝ^m} F(J(x,1) ι(k)) dx dk`. Moving `dlast(s)` to the left
   (`iotaGL_mul_dlastGL`, `chartGL_mul_dlastGL`, `apply_dlastGL_mul`) gives
   `F(J(x,1)ι(k)) = c'_s · Φ_s(k, x)` with
   `Φ_s(k, x) = u(J(s⁻¹x, 1) ι(k)) · H(J(x,1) ι(k))` and a constant `c'_s ≠ 0`.
   Since `chartConstant m ≠ 0`, `∫_{O(m)} ∫ Φ_s(k, x) dx dk = 0` for every `s > 0`.
2. **Domination.** Let `|u| ≤ C_u` on `O(m+1)`. For `s ≥ 1`, the Library's
   `norm_le_partialSq` (for the dual exponents `−e`) and `RealSphericalChart.regularized_chart`
   give
   `|Φ_s(k, x)| ≤ C_u ∏ r_{l+1}(s⁻¹x)^{ε^u_l} · r_m(x)^{−1} ∏ r_{l+1}(x)^{ε^h_l}`,
   with `ε^u_l = chartExponent (−e) l`, `ε^h_l = chartExponent e l`, `ε^u_l + ε^h_l = −1`, and
   `ε^h_l ≤ −1/2` by weak dominance. `prod_rpow_mul_prod_rpow_le_half` bounds each factor by
   `r_{l+1}(x)^{−1/2}`. With `A = r_{l+1}(s⁻¹x)` and `B = r_{l+1}(x)`, so that `1 ≤ A ≤ B`
   (`partialSq_smul_le`):
   - if `ε^u_l ≥ 0`, then `A^{ε^u} B^{ε^h} ≤ B^{−1} ≤ B^{−1/2}`;
   - otherwise `A^{ε^u} B^{ε^h} ≤ B^{ε^h} ≤ B^{−1/2}`.
   So `|Φ_s(k, x)| ≤ D(x) = C_u ‖partialSqProd (−1/2, …, −1/2) (−1) x‖`.
   `D` is integrable, because `TailCondition (−1/2) (−1)` holds (`tailCondition_half`) and the
   Library's `integrable_and_integral_ne_zero` applies.
3. **Limit.** Take `s = n + 1 → ∞`. Then `s⁻¹x → 0`, `J(0, 1) = 1` and `u` is continuous.
   Dominated convergence, applied twice (inner `dx` with bound `D`, outer `dk` with the
   constant bound `∫ D`), turns the vanishing integrals of step 1 into
   `∫_{O(m)} u(ι(k)) · (T H)(k) dk = 0`. Here `T H` is the partial Jacquet integral.
4. **Conclusion.** By `RealSphericalChart.jacquetStep_regularized`, `(T H)(k)` is the constant
   `∫ partialSqProd (chartDiff e) (−1)` for `k ∈ O(m)`. This constant is nonzero by
   `integral_regularized_ne_zero`, which uses weak dominance. So `∫_{O(m)} u(ι(k)) dk = 0`.

## Provenance

The argument is the limit argument of the Library's `JacquetLimit`, written for the strict
Langlands lemma. The new part is the domination for weakly dominant exponents:
the extra factor `r_m(x)^{−1}` of `H` and the per-factor bound by `r_{l+1}^{−1/2}`.
