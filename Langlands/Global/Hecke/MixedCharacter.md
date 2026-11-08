# The product character on the mixed space

Module `Langlands.Global.Hecke.MixedCharacter`, namespace `Langlands.Global.Hecke`.

Throughout, `K` is a number field, `V = mixedSpace K = ℝ^{real places} × ℂ^{complex places}`
with Lebesgue measure, `N = mixedEmbedding.norm`, and `C = fundamentalCone K`. The functions
`realCharFun p t x = (x / |x|)^p |x|^t`, `complexCharFun N u z = (z / |z|)^N |z|^{2u}`,
`realGaussian b p x = x^p e^{-π b x²}`, `complexGaussian b N z` (`z̄^N e^{-2π b |z|²}` for `N ≥ 0`,
`z^{|N|} e^{-2π b |z|²}` for `N < 0`), the product character
`mixedCharFun p t N u x = ∏_v realCharFun (p v) (t v) (x_v) ∏_v complexCharFun (N v) (u v) (z_v)`
and the product Gaussian `mixedGaussian aR aC p N` are defined in
`Langlands.Global.Hecke.ArchGaussian` and `Langlands.Global.Hecke.MixedSpaceFourier`. Here
`x / |x|` is the real quotient (so `0 / 0 = 0`) and complex powers of nonnegative reals are
Mathlib's `cpow`.

This module collects the properties of the product character used to build the theta data of
the Hecke global functional equation on the fundamental cone, and the integrability of the
archimedean zeta integrand. It is an internal helper module and states nothing about
`L`-functions.

## Provenance

Internal helper for the proof of the published actual Hecke global functional equation
statement. The facts are elementary properties of quasi-characters of `ℝ^×` and `ℂ^×` (Tate's
thesis, Cassels–Fröhlich 1967, §2.3, describes these quasi-characters) and the convergence of the
archimedean Tate zeta integrals of Gaussians for `Re(s + t) + p > 0`, resp.
`Re(s + u) + |N|/2 > 0` (Tate's computations "k Real" and "k Complex", §2.5, pp. 316–319). The
statements are formulated for the internal assembly.

## Definitions

- `mixedCharTwo p t N u = mixedCharFun p t N u (2 • 1)`, the doubling constant of the product
  character (`2 • 1` is the point of `V` all of whose coordinates are `2`).

## Main results

### The real and complex characters

- `realCharFun_mul`, `realCharFun_one`: `realCharFun p t` is multiplicative on all of `ℝ` and
  takes the value `1` at `1`.
- `norm_realCharFun`: `|realCharFun p t x| = |x|^{Re t}` for `x ≠ 0`.
- `complexCharFun_mul`, `complexCharFun_one`, `norm_complexCharFun`: the same for
  `complexCharFun N u` on `ℂ`, with `|complexCharFun N u z| = |z|^{2 Re u}` for `z ≠ 0`.
- `measurable_realCharFun`, `measurable_complexCharFun`.

### The product character

- `mixedCharFun_mul`, `mixedCharFun_one`: `χ(x y) = χ(x) χ(y)` for all `x, y ∈ V`, and `χ(1) = 1`.
- `measurable_mixedCharFun`.
- `mixedCharFun_ne_zero`: `χ(x) ≠ 0` if all coordinates of `x` are nonzero.
- `mixedCharFun_two_smul`, `mixedCharTwo_ne_zero`: `χ(2 • x) = mixedCharTwo p t N u · χ(x)` and
  `mixedCharTwo p t N u ≠ 0`.
- `rpow_le_max_mul_rpow`: if `0 < r`, `0 < M` and `r M ≤ y ≤ R M`, then
  `y^a ≤ max(r^a, R^a) M^a` for every real `a`.
- `exists_norm_mixedCharFun_le_cone`: there are `K_χ, τ` with `|χ(x)| ≤ K_χ N(x)^τ` for all
  `x ∈ C`.

### Integrability

- `integrable_norm_rpow_mul_exp_neg_mul_sq`: on a nontrivial finite-dimensional real normed space
  with an additive Haar measure, `x ↦ ‖x‖^α e^{-b ‖x‖²}` is integrable for `b > 0` and
  `α > -dim`.
- `ae_ne_zero_real`, `ae_ne_zero_complex`: almost every real (complex) number is nonzero.
- `integrable_realGaussian_mul_realCharFun`: for `b > 0` and `Re(s + t + p) > 0`,
  `x ↦ realGaussian b p x · realCharFun p t x · |x|^{s-1}` is integrable on `ℝ`.
- `integrable_complexGaussian_mul_complexCharFun`: for `b > 0` and `Re(s + u + |N|/2) > 0`,
  `z ↦ complexGaussian b N z · complexCharFun N u z · |z|^{2(s-1)}` is integrable on `ℂ`.
- `integrable_mixedGaussian_mul_mixedCharFun`: for nonzero scales and `s` with
  `Re(s + t_v + p_v) > 0` at the real places and `Re(s + u_v + |N_v|/2) > 0` at the complex places
  (the hypotheses of `integral_mixedGaussian_mul_mixedCharFun`),
  `x ↦ mixedGaussian aR aC p N x · mixedCharFun p t N u x · N(x)^{s-1}` is integrable on `V`.

## Proofs

**Characters.** For real `x, y`, `(x y)/|x y| = (x/|x|)(y/|y|)` and
`|x y|^t = |x|^t |y|^t` (`mul_cpow_ofReal_nonneg`); for complex `z, w` similarly with `zpow`. The
norms follow from `|x/|x|| = 1` for `x ≠ 0` and `|r^t| = r^{Re t}` for `r > 0`. Measurability is
by `fun_prop`. The product statements multiply the coordinatewise ones; `2 • x = (2 • 1) x`
(`smul_one_mul`) gives the doubling relation, and the coordinates of `2 • 1` are `2 ≠ 0`.

**Cone bound.** By `exists_normAtPlace_bounds` (from `MixedSpaceUnfolding`) every coordinate of
`x ∈ C` lies between `r M` and `R M`, `M = N(x)^{1/[K:ℚ]}`. Hence `|x_v|^{Re t_v} ≤ C_v M^{Re t_v}`
and `|z_v|^{2 Re u_v} ≤ D_v M^{2 Re u_v}` (`rpow_le_max_mul_rpow`, using monotonicity of
`y ↦ y^a` for `a ≥ 0` and antitonicity for `a < 0`), and multiplying gives
`|χ(x)| ≤ (∏ C_v ∏ D_v) N(x)^τ` with `τ = [K:ℚ]⁻¹ (Σ Re t_v + Σ 2 Re u_v)`.

**Integrability.** By `integrable_fun_norm_addHaar`, `‖x‖^α e^{-b‖x‖²}` is integrable iff
`y^{α + dim - 1} e^{-b y²}` is integrable on `(0, ∞)`, which is Mathlib's
`integrableOn_rpow_mul_exp_neg_mul_sq` for `α + dim - 1 > -1`. Away from `0`, the norm of the real
integrand is `|x|^{p + Re t + Re s - 1} e^{-π b x²}` and that of the complex integrand is
`|z|^{|N| + 2 Re u + 2(Re s - 1)} e^{-2π b |z|²}` (`N.toNat + (-N).toNat = |N|`), so both are
dominated by integrable functions (`Integrable.mono'`). On `V`, the integrand factors as the
product of the one-variable integrands over the coordinates (as in the proof of
`integral_mixedGaussian_mul_mixedCharFun`), so `Integrable.fintype_prod` and
`Integrable.mul_prod` apply on `volume = (Measure.pi volume).prod (Measure.pi volume)`.
