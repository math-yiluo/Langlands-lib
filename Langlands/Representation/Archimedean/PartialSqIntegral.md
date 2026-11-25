# Iterated integrals of products of powers of partial square sums on `ℝ^m`

Lean module: `Langlands.Representation.Archimedean.PartialSqIntegral`.

This module was written for the proof of
`RealStandardIrreducibleCriterionStatement`. It is the analytic input to the nonvanishing of the
full Jacquet integral on the minimal-`K`-type test vector of a real principal series. That
nonvanishing is used in the proof of `RealReverseIntertwinerKernelStatement`: an intertwiner from a
standard module to the reversed one kills every proper `(g, K)`-submodule. On the chart
`x ↦ J(x, 1)` of the opposite unipotent radical, the integrand of that Jacquet integral is a product
of complex powers of the Gram determinants `r_l(x)`. This module proves that such an iterated
integral converges and does not vanish.

Notation: `partialSq x l = 1 + ∑_{j<l} x_j²` for `x ∈ ℝ^m`
(`Langlands.Archimedean.ParabolicChartBound.partialSq`, written `r_l(x)` below). Declarations
without a prefix are in the namespace `Langlands.Archimedean.PartialSqIntegral`. Complex powers
are `Complex.cpow` of the positive reals `r_l(x)`, i.e. `r^d = exp(d log r)`.

Provenance. This is derived internal infrastructure with no literature source. It is an elementary
iterated integral: the real rank-one case of the Gindikin–Karpelevich computation, written out on
the chart of the opposite unipotent radical of `P_{m,1}`. The module makes no literature claim. Its
complex-chart analogue, which only proves integrability, is the Library module
`Langlands.Representation.Archimedean.ComplexPartialSqIntegral`, and steps 3–4 below follow that
module's induction.

## Main results

- `lineIntegral d = ∫_ℝ (1 + t²)^d dt` (complex `d`).
- `integrable_add_sq_cpow`: for `a > 0` and `Re d < −1/2`, `t ↦ (a + t²)^d` is integrable on `ℝ`.
- `lineIntegral_mul_Gamma`: for `Re d < −1/2`, `β(d) Γ(−d) = √π Γ(−d − 1/2)`.
- `lineIntegral_ne_zero`: for `Re d < −1/2`, `β(d) ≠ 0`.
- `integral_add_sq_cpow`: for `a > 0` and every `d`, `∫_ℝ (a + t²)^d dt = a^{d + 1/2} β(d)`.
  `integral_add_sq_rpow` is the same scaling identity for real exponents.
- `partialSqProd d c x = r_m(x)^c ∏_{l<m} r_{l+1}(x)^{d_l}` for `d : Fin m → ℂ`, `c ∈ ℂ`.
- `TailCondition d c`: `Re c + ∑_{l ≥ j} (Re d_l + 1/2) < 0` for every `j < m`. In Lean the tail
  sum is written `∑_l (if j ≤ l then Re d_l + 1/2 else 0)`.
- `integrable_and_integral_ne_zero m d c`: under `TailCondition d c`, `partialSqProd d c` is
  integrable on `ℝ^m` (Lebesgue measure, `volume` on `Fin m → ℝ`) and its integral is nonzero.
- `integrable_and_integral_prod_ne_zero`: the case `c = 0`. If
  `∑_{l ≥ j} (Re d_l + 1/2) < 0` for every `j`, then `x ↦ ∏_{l<m} r_{l+1}(x)^{d_l}` is integrable
  on `ℝ^m` and its integral is nonzero.

Helper lemmas: `continuous_ofReal_cpow` (for a continuous positive real function `f` on any
topological space, `x ↦ f(x)^d` is continuous), `one_div_cpow`, `ofReal_sqrt_eq_cpow`,
`partialSq_snoc_castSucc`, `partialSq_snoc_last`, `continuous_partialSq`,
`continuous_partialSqProd`, `norm_partialSqProd`, and the Fubini lemmas `measurable_integrand`,
`norm_integrand`, `integral_norm_integrand`, `integrable_integrand`, `integral_gaussian_mul` for
step 1.

## Proof

1. **`β(d) ≠ 0`** (`one_add_sq_cpow_mul_Gamma`, `lineIntegral_mul_Gamma`, `lineIntegral_ne_zero`).
   For `Re d < 0`, the Gamma integral `∫_0^∞ u^{s−1} e^{−ru} du = Γ(s) r^{−s}`
   (`Complex.integral_cpow_mul_exp_neg_mul_Ioi`) with `s = −d` and `r = 1 + t²` gives
   `(1 + t²)^d Γ(−d) = ∫_0^∞ u^{−d−1} e^{−u} e^{−u t²} du`. The function
   `(t, u) ↦ u^{−d−1} e^{−u} e^{−ut²}` is integrable on `ℝ × (0, ∞)` when `Re d < −1/2`. Its
   `t`-integral is the Gaussian integral `√(π/u) |u^{−d−1}| e^{−u}`, and the `u`-integral of that
   converges as a real Gamma integral with parameter `−Re d − 1/2 > 0`
   (`integrable_prod_iff'`, `integral_gaussian`, `Real.GammaIntegral_convergent`). Swapping the
   integrals (`integral_integral_swap`) and doing the Gaussian integral first gives
   `β(d) Γ(−d) = √π ∫_0^∞ e^{−u} u^{(−d−1/2)−1} du = √π Γ(−d − 1/2)`
   (`Complex.Gamma_eq_integral`). Since `Re(−d − 1/2) > 0`, `Γ(−d − 1/2) ≠ 0`
   (`Complex.Gamma_ne_zero_of_re_pos`), so `β(d) ≠ 0`.
2. **Integrability and scaling in one variable** (`integrable_add_sq_cpow`,
   `integral_add_sq_cpow`, `integral_add_sq_rpow`). `|(a + t²)^d| = (a + t²)^{Re d}
   = a^{Re d} (1 + (t/√a)²)^{Re d}`. This is integrable because
   `t ↦ (1 + t²)^{Re d}` is integrable for `Re d < −1/2`
   (`ParabolicChartBound.integrable_one_add_sq_rpow`, `Integrable.comp_div`). The substitution
   `t = √a s` (`Measure.integral_comp_mul_left`) and `(a(1 + s²))^d = a^d (1 + s²)^d`
   (`Complex.mul_cpow_ofReal_nonneg`) give `∫ (a + t²)^d dt = √a a^d β(d) = a^{d+1/2} β(d)`.
3. **The last coordinate** (`partialSq_snoc_castSucc`, `partialSq_snoc_last`). For
   `x = Fin.snoc y t` with `y ∈ ℝ^m`, `t ∈ ℝ`: `r_{l+1}(x) = r_{l+1}(y)` for `l < m`, and
   `r_{m+1}(x) = r_m(y) + t²`.
4. **Induction on `m`** (`integrable_and_integral_ne_zero`). For `m = 0`, `partialSqProd d c` is
   the constant `1` (`r_0 = 1`) on the one-point space `ℝ^0` of measure `1`, so its integral is
   `1 ≠ 0`. For `m + 1`, put `β = c + d_m` and `d' = (d_0, …, d_{m−1})`. The condition at `j = m` is
   `Re β < −1/2`. The condition for `(d', β + 1/2)` at `j < m` is the old condition at the same `j`,
   so the induction hypothesis applies to `partialSqProd d' (β + 1/2)`. Split
   `ℝ^{m+1} ≅ ℝ × ℝ^m` with the last coordinate first (`MeasurableEquiv.piFinSuccAbove` at
   `Fin.last m`, measure preserving by `volume_preserving_piFinSuccAbove`). By step 3 and
   `r^{c + d_m} = r^c r^{d_m}`, the integrand becomes
   `H(t, y) = (r_m(y) + t²)^β ∏_{l<m} r_{l+1}(y)^{d'_l}`. By step 2:
   - each `t ↦ H(t, y)` is integrable with integral `β(β) · partialSqProd d' (β + 1/2) y`;
   - `∫ |H(t, y)| dt = (∫ (1 + s²)^{Re β} ds) · |partialSqProd d' (β + 1/2) y|`, which is
     integrable in `y` by the induction hypothesis.

   So `H` is integrable on `ℝ × ℝ^m` (`integrable_prod_iff'`), and hence so is `partialSqProd d c`
   (`MeasurePreserving.integrable_comp_emb`). By Fubini (`integral_prod_symm`),
   `∫ partialSqProd d c = β(β) · ∫ partialSqProd d' (β + 1/2)`. Both factors are nonzero, by
   step 1 and the induction hypothesis.
5. `integrable_and_integral_prod_ne_zero` is step 4 with `c = 0`, since `r_m^0 = 1`.
