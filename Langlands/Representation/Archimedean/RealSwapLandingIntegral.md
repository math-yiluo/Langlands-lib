# The landing integral for the blocks `[induced d, character c]`

Lean module: `Langlands.Representation.Archimedean.RealSwapLandingIntegral`, namespace
`Langlands.Archimedean.RealSwapLandingIntegral`.

## Role and provenance

This module is an internal step in the proof of
`Langlands.Archimedean.RealCharacterInducedFiltrationStatement`. It proves the
hypothesis `RealSwapLandingAlgebra.SpecialLanding` (theorem `specialLanding`). With
`RealSwapLandingAlgebra.inducedFirst_of_special`, this gives
`RealSwapLandingInducedFirstStatement` (theorem `inducedFirst`), one half of the landing
statement `RealSwapLandingStatement`.

`SpecialLanding` asks, for each `f` in the `O(3)`-finite standard module of
`[induced d, character c]` and each `n ∈ ℕ`, for two multipliers `μ₁`, `μ₀` of prescribed
recurrence and symmetry type, and continuous functions `h`, `u` with
`Φ¹_k h = μ₁(k) Φ¹_k f` and `Φ⁰_k u = μ₀(k) Φ⁰_k h` on `O(3)`, such that `Φ¹_k u = 0` on
`O(3)` for `|k| < ℓ`. The proof takes `μ₁ = ĉ_n`, `μ₀ = ĉ_{n+ℓ}`, `h = C¹_n f'` and
`u = C⁰_{n+ℓ} C¹_n f'`, where `f'` agrees with `f` on `O(3)` but has its character block's
exponent changed to `s = t - ℓ/2 - (n + 1)`. With this exponent the three exponents
`t + ℓ/2, t - ℓ/2, s` have strictly decreasing real parts, so `f'` is integrable over the chart
`ℝ²` of the opposite unipotent radical of the parabolic subgroup of type `(2, 1)`. Up to a sign, `u`
equals the chart integral `∫_{ℝ²} f'(chartGL v · w · x) dv` on `O(3)`. Moving `r_1(θ)` through this integral
turns `Φ¹_k u` into an integral over `ℝ²` of `Φ⁰_k f'`, and `Φ⁰_k f'` vanishes for `|k| < ℓ`
because `f'` lies in a standard module.

The argument is an explicit computation with integrals over the chart in `GL_3(ℝ)`
coordinates, designed for this proof. The module formalizes no literature statement, so it
has no sources. All declarations are auxiliary lemmas
proved here from Mathlib, Library results and the companion modules `RealSwapLandingKernel`,
`RealSwapLandingRankOne`, `RealSwapLandingMatrices` and `RealSwapLandingAlgebra`.

## Notation

- `GL_3(ℝ)` is `Langlands.GeneralLinear 3 ℝ`. `O(3)` is the subgroup `unitaryCompact ℝ 3`.
- `r_p(θ) = blockRotation 3 p θ` is the rotation in the coordinates `p, p + 1`.
- `Φ^p_k F (g) = blockFourierCoefficient 3 p k F g = ∫₀^{2π} F(r_p(θ) g) e^{-ikθ} dθ`.
- `ĉ_r = sinKernel r` and `C^r_p F = kernelOp 3 p r F`, with
  `C^r_p F (g) = ∫₀^π sin^r θ F(r_p(θ) g) dθ` (`RealSwapLandingKernel`).
- `chartGL v` is the lower unipotent matrix with last row `(v₀, v₁, 1)`. `w = wPerm`,
  `n̄₀`, `n̄₁`, `s₀`, `s₁` and `rotInv θ` are the matrices of `RealSwapLandingMatrices`.
- For complex character data `d`: `ℓ = |m|` is `d.weight.natAbs` and `t` is `d.exponent`.
  `charData e s` is the real character `x ↦ sgn(x)^e |x|^s` (`RealJacquetFrobenius`).
- `posChar d e s` (`RealSwapLandingMatrices`) is the family of position characters
  `realPositionCharacter [induced d, character (charData e s)]`.

## Declarations

### Membership in the standard module of `[induced d, character c]`

- `realInducedBlockAt_induced_character`: the only induction block of `[d, c]` starts at
  position `0` and has data `d`. Proof: case analysis on the position.
- `mem_realStandardModule_induced_character`: if `f` lies in the principal series of the
  position characters of `[d, c]` and `Φ⁰_k f = 0` on `O(3)` for every `|k| < ℓ`, then `f`
  lies in the standard module of `[d, c]`. The standard module asks `Φ⁰_k f (g) = 0` for all
  `g ∈ GL_3(ℝ)` and `|k| < ℓ` (`mem_realStandardModule_iff`). Proof: if `(-1)^k` differs from
  the product of the two position characters of the block at `-1`, then `Φ⁰_k f = 0` by the
  parity lemma `blockFourierCoefficient_eq_zero_of_parity`. Otherwise `k ≡ ℓ + 1 (mod 2)`, so `k` lies in the
  window `{|k| < ℓ, k ≡ ℓ + 1 (mod 2)}` (`RealBlockFourierPropagation.window`). Then the
  Library propagation lemma `blockFourierCoefficient_window_eq_zero` extends the vanishing
  from `O(3)` to all of `GL_3(ℝ)`. Its hypotheses are smoothness, the exponential
  equivariance `IsExpEquivariant α f` of principal series functions
  (`isExpEquivariant_of_mem_principalSeries`, with `α_i` the position exponent plus
  `(3 - 1)/2 - i`), and `α_0 - α_1 = (t + ℓ/2 + 1) - (t - ℓ/2) = ℓ + 1`.

### Changing the exponent of the character block

- `exists_extension`: for `f` in the `O(3)`-finite standard module of `[d, c]` and any
  `s ∈ ℂ`, there is `f'` in the `O(3)`-finite standard module of
  `[d, charData (parity c) s]` with `f' = f` on `O(3)`. Proof: the restriction `φ` of `f` to
  `O(3)` is a polynomial in the matrix entries (`OrthogonalFinitePolynomial`), so its right
  translates span a finite-dimensional space (`TranslateFinite`). The two lists of position
  characters agree on signs, since `|±1|^s = 1`. So `φ` has the sign-equivariance required
  by `PrincipalSeriesExtension.principalSeriesExtension`. That theorem gives an `O(3)`-finite
  `f'` in the principal series of `[d, charData (parity c) s]` with `f' = φ` on `O(3)`. Its
  Fourier coefficients `Φ⁰_k` on `O(3)` equal those of `f`, because `r_0(θ) g ∈ O(3)`
  (`RealSwapFLanding.blockFourierCoefficient_congr`). So the previous lemma puts `f'` in the
  standard module.

### Analytic helpers

- `continuous_of_mem_principalSeries`: functions of a principal series of `GL_3(ℝ)` are
  continuous (they are smooth).
- `continuous_rotInv`: `θ ↦ rotInv θ` is continuous.
- `norm_exp_neg_mul_I`: `|e^{-ikθ}| = 1` for real `θ`.
- `isStrictlyDominant`: for `ℓ ≥ 1` and `s = t - ℓ/2 - (n + 1)`, the position exponents
  `t + ℓ/2, t - ℓ/2, s` of `[d, charData e s]` have strictly decreasing real parts
  (`IsStrictlyDominant … 2`). The steps are `ℓ > 0` and `ℓ/2 + n + 1 - ℓ/2 > 0`.

### The chart integral

From here on, `s = t - ℓ/2 - (n + 1)` and `f` lies in the principal series `posChar d e s`
(or in the standard module of `[d, charData e s]`).

- `chartIntegral f x = ∫_{ℝ²} f(chartGL v · w · x) dv` (Bochner integral over `Fin 2 → ℝ`).
- `chartIntegral_eq`: for `ℓ ≥ 1` and `x ∈ O(3)`,
  `chartIntegral f x = (-1)^{ℓ+1} C⁰_{n+ℓ} C¹_n f (x)`. Proof: `w x ∈ O(3)` and the
  exponents are strictly dominant, so the integrand is integrable (Library
  `PartialJacquet.integrable_chart`). Identify `ℝ²` with `ℝ × ℝ` by the measure-preserving
  map `MeasurableEquiv.finTwoArrow` and apply Fubini (`integral_prod`). By
  `chartGL_mul_wPerm`, `chartGL v · w = n̄₁(v₁) s₁ · n̄₀(v₀) s₀`. The inner integral over
  `v₁` is then `C¹_n f(n̄₀(v₀) s₀ x)` (`integral_nbar1`). The outer integral over `v₀` is
  `(-1)^{ℓ+1} C⁰_{n+ℓ}(C¹_n f)(x)`, by `RealSwapLandingRankOne.integral_eq_kernelOp` with the
  transformation law `kernelOp_nbar0_cotan`.
- `integrable_landing`: for `ℓ ≥ 1`, `κ ∈ O(3)` and `k ∈ ℤ`, the function
  `(θ, v) ↦ f(r_0(θ) · chartGL v · κ) e^{-ikθ}` is integrable on `(0, 2π] × ℝ²`. Proof: the
  function `G(θ, v) = f(chartGL v · r_0(θ) κ) e^{-ikθ}` is continuous. Because
  `r_0(θ) κ ∈ O(3)`, it is bounded by `C ∏_l (1 + v_l²)^{a_l}`, the Library bound
  `norm_le_of_mem_principalSeries` with the chart exponents `a_l`. This bound is integrable
  (`ParabolicChartBound.integrable_prod_one_add_sq_rpow`). So `G` is integrable. The map
  `(θ, v) ↦ (θ, v · rotInv θ)` preserves the product measure: it is a skew product
  (`MeasurePreserving.skew_product`) of the identity with linear maps of determinant `1`
  (`map_vecMulEquiv`). By `rot0_mul_chartGL`,
  `r_0(θ) · chartGL v = chartGL (v · rotInv θ) · r_0(θ)`, so the given function is `G` composed
  with this map.
- `blockFourierCoefficient_chartIntegral`: for `ℓ ≥ 1`, `f` in the standard module of
  `[d, charData e s]`, `g ∈ O(3)` and `|k| < ℓ`, `Φ¹_k (chartIntegral f)(g) = 0`. Proof: by
  `wPerm_mul_rot1`, `w r_1(θ) = r_0(θ) w`. The linear change of variables `v ↦ v · rotInv θ`
  has determinant `1` (`PartialJacquet.integral_vecMul_eq`). With `rot0_mul_chartGL` these
  give `chartIntegral f (r_1(θ) g) = ∫_{ℝ²} f(r_0(θ) · chartGL v · w g) dv`. Exchange the
  `θ`- and `v`-integrals (`intervalIntegral_integral_swap`, justified by
  `integrable_landing`). The result is `∫_{ℝ²} Φ⁰_k f(chartGL v · w g) dv`, and its integrand vanishes
  because `f` lies in the standard module and `|k| < ℓ`.
- `landing`: under the same hypotheses, `Φ¹_k (C⁰_{n+ℓ} C¹_n f)(g) = 0`. Proof: on `O(3)`,
  `C⁰_{n+ℓ} C¹_n f = (-1)^{ℓ+1} chartIntegral f` (`chartIntegral_eq` and
  `((-1)^{ℓ+1})² = 1`). Since `r_1(θ) g ∈ O(3)`, the Fourier coefficient `Φ¹_k` at `g` only
  sees values on `O(3)` (`RealSwapFLanding.blockFourierCoefficient_congr`). The constant sign
  factors out of the integral, and `blockFourierCoefficient_chartIntegral` gives `0`.

### The special landing

- `specialLanding : RealSwapLandingAlgebra.SpecialLanding`. Proof: given `c`, `d`, `f` and
  `n`, take `s = t - ℓ/2 - (n + 1)` and `f'` from `exists_extension`. Take `μ₁ = ĉ_n`,
  `μ₀ = ĉ_{n+ℓ}`, `h = C¹_n f'` and `u = C⁰_{n+ℓ} C¹_n f'`.
  - Recurrence and symmetry: `isRecurrent_sinKernel` and `isSymmetric_sinKernel`. For `μ₀`
    the recurrence parameter is `(n + ℓ) + 2 = n + 2 + ℓ`.
  - Non-vanishing at `0` and `1`: `sinKernel_zero_ne_zero` and `sinKernel_one_ne_zero`.
  - Continuity: `continuous_kernelOp`, since `f'` is continuous.
  - Multiplier identities: `blockFourierCoefficient_kernelOp` gives `Φ¹_k h = ĉ_n(k) Φ¹_k f'`
    and `Φ⁰_k u = ĉ_{n+ℓ}(k) Φ⁰_k h`. On `O(3)`, `Φ¹_k f' = Φ¹_k f`, because `f' = f` there.
  - Landing: if `ℓ = 0` there is no `k` with `|k| < 0`. Otherwise apply `landing` to `f'`.
- `inducedFirst : RealSwapLandingInducedFirstStatement`. This is
  `RealSwapLandingAlgebra.inducedFirst_of_special specialLanding`.
