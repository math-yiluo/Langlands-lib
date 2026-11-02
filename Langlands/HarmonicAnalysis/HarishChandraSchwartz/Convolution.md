# Convolution on the Harish-Chandra Schwartz space (Lemma III.6.1)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.Convolution`,
namespace `Langlands.HarishChandraSchwartz`. It builds on
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.Basic` (the seminorms `ν_r`, the
levels `C_H`, the space `C(G)` and its LF topology),
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.Spherical` (the measure
`normalizedHaar K`) and `Langlands.HarmonicAnalysis.HarishChandraSchwartz.TestFunctions`
(`IsBiInvariant.isLocallyConstant`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, section III.6 (printed
pp. 271–272, PDF pp. 37–38). For `f₁, f₂ ∈ C_lisse(G)` such that the integral
`∫_G f₁(h) f₂(h⁻¹ g) dh` converges absolutely for every `g`, Waldspurger writes
`f₁ * f₂ (g)` for its value. Lemma III.6.1 states:

> For `f₁, f₂ ∈ C(G)` the integral above converges absolutely for every `g ∈ G`. The
> function `f₁ * f₂` lies in `C(G)`. The map `C(G) × C(G) → C(G)`,
> `(f₁, f₂) ↦ f₁ * f₂`, is separately continuous in each variable.

The proof uses the inequality `1 + σ(g) ≤ (1 + σ(h)) (1 + σ(h⁻¹ g))` and Lemmas II.1.3
(`∫_K Ξ(g₁ k g₂) dk = Ξ(g₁) Ξ(g₂)`), II.1.4 (`Ξ(g) = Ξ(g⁻¹)`) and II.1.5 (there is
`d ∈ ℕ` with `∫_G Ξ(g)² (1 + σ(g))^{-d} dg < ∞`), all on printed p. 252, PDF p. 18.
Here `dh` is the Haar measure of `G` and `dk` the Haar measure of `K` of total mass one
(I.1).

## Scope: generic weights and explicit hypotheses

The weights `Ξ σ : G → ℝ` are arbitrary, as in `Basic`. The measure `μ` on `G` is any
left-invariant s-finite measure; it plays the role of the Haar measure `dh`. `K` is any
compact subgroup of `G`; it plays the role of Waldspurger's maximal compact subgroup.
The properties of the weights that the proof uses are collected in the hypothesis
structure `ConvolutionWeights μ K Ξ σ`:

- `pos`, `nonneg`, `continuous_xi`, `continuous_sigma`: `Ξ > 0`, `σ ≥ 0`, both
  continuous;
- `one_add_le`: `1 + σ(g) ≤ (1 + σ(h)) (1 + σ(h⁻¹ g))` for all `g, h`;
- `xi_mul_left`, `sigma_mul_left`: `Ξ(k g) = Ξ(g)` and `σ(k g) = σ(g)` for `k ∈ K`;
- `xi_inv`: `Ξ(g⁻¹) = Ξ(g)` (Lemma II.1.4);
- `integral_xi`: `∫_K Ξ(g₁ k g₂) dk = Ξ(g₁) Ξ(g₂)` for the measure
  `normalizedHaar K` (Lemma II.1.3);
- `square`: there is `d ∈ ℕ` with `∫_G Ξ(g)² (1 + σ(g))^{-d} dμ(g) < ∞`
  (Lemma II.1.5, for the same measure `μ` as the convolution).

These are hypotheses of this module. They are not proved here for Waldspurger's `Ξ` and
`σ`, and the module does not realize those weights. For the source weights they are
open proof obligations, to be discharged by the modules that construct `Ξ` and `σ` on a
reductive `p`-adic group:

- For `σ = height τ` (`Height`), `height_nonneg`, `continuous_height` (for continuous
  `τ`) and `one_add_height_le` give `nonneg`, `continuous_sigma` and `one_add_le`, and
  `height_mul_mul` gives `sigma_mul_left` when `K ≤ heightSubgroup τ`, that is, when
  `τ(K) ⊆ GL_n(𝒪)` as in I.1.
- For `Ξ = xi hPK δ` (`Spherical`), with `δ` trivial on `P ∩ K` and `K` open, `xi_pos`,
  `continuous_xi` and `xi_mul_left` give `pos`, `continuous_xi` and `xi_mul_left`, and
  `integral_xi_mul_mul` (with `G` second countable) gives `integral_xi`.
- Lemma II.1.4 (`xi_inv`) and Lemma II.1.5 (`square`) are not proved in any of these
  modules. Waldspurger derives II.1.4 from `π̌ = π` and proves II.1.5 with the Cartan
  decomposition (I.1 (4)); both remain open proof obligations.

The generic lemma `one_add_le_of_le_add` derives `one_add_le` from `σ ≥ 0` and
subadditivity `σ(g h) ≤ σ(g) + σ(h)`.

## Definitions

- `ConvolutionWeights μ K Ξ σ`: the hypothesis structure above (a `Prop`).
- `convolution μ f₁ f₂ g = ∫_G f₁(h) f₂(h⁻¹ g) dμ(h)`, an alias of the existing
  [`Hecke.convolutionIntegral`](../../Representation/Hecke/Convolution.md), a Bochner integral of complex
  functions. Where the integrand is not integrable its value is `0`; Waldspurger defines
  `f₁ * f₂` only when the integral converges absolutely. For `f₁, f₂ ∈ C(G)` the
  integrand is integrable (`integrable_mul_of_mem_schwartzSubmodule`), so the two agree.
  Mathlib's `MeasureTheory.mlconvolution` uses the same formula for `ℝ≥0∞`-valued
  functions and the lower Lebesgue integral.
- `ConvolutionWeights.squareExponent hw`: the exponent `d` chosen from `square`.
- `Level.convolutionLeft hw h₂ H₁`: for `f₂ ∈ C_{H₂}`, the linear map
  `f₁ ↦ f₁ * f₂` from `C_{H₁}` to `C_{H₁ ∩ H₂}`. `Level.convolutionRight hw h₁ H₂` is
  the map `f₂ ↦ f₁ * f₂` from `C_{H₂}` to `C_{H₁ ∩ H₂}` for `f₁ ∈ C_{H₁}`.
- `Space.convolution hw f₁ f₂ : Space Ξ σ`: the product `f₁ * f₂` on `C(G)`, and
  `Space.convolutionBilin hw`: the same product as a `ℂ`-bilinear map.

## Results

The hypotheses are listed per group of results.

For a group `G` with a measurable structure and any measure `μ`, unless stated
otherwise:

- `convolution_smul_left`, `convolution_smul_right`: `(c f₁) * f₂ = c (f₁ * f₂)` and
  `f₁ * (c f₂) = c (f₁ * f₂)`.
- `convolution_add_left`, `convolution_add_right`: additivity in each variable, assuming
  the two integrands are integrable for every `g`.
- `IsBiInvariant.convolution` (`μ` left invariant, measurable multiplication): if `f₁`
  and `f₂` are `H`-bi-invariant, so is `f₁ * f₂`.
- `weight_mul_ofReal`, `enorm_le_nu_mul` (`Ξ > 0`, `σ ≥ 0`, no group structure used):
  `|f(g)| ≤ ν_r(f) Ξ(g) (1 + σ(g))^{-r}`.
- `one_add_le_of_le_add`, described above.

The following results take `hw : ConvolutionWeights μ K Ξ σ`, with `G` a topological
group with its Borel σ-algebra and `K` compact:

- `ConvolutionWeights.rpow_le` (`r ≥ 0`):
  `(1 + σ(h⁻¹ g))^{-r} ≤ (1 + σ(g))^{-r} (1 + σ(h))^r`.
- `ConvolutionWeights.enorm_mul_le` (`r ≥ 0`, any `r'`): the pointwise bound
  `|f₁(h) f₂(h⁻¹ g)| ≤ ν_{r'}(f₁) ν_r(f₂) (1 + σ(g))^{-r} Ξ(h) Ξ(h⁻¹ g) (1 + σ(h))^{r - r'}`.
- `ConvolutionWeights.lintegral_square_lt_top`: the integral of `square` is finite for
  `d = squareExponent`.

The following results also assume `G` second countable and `μ` left invariant and
s-finite:

- `ConvolutionWeights.lintegral_xi_mul_xi` (any real `s`):
  `∫_G Ξ(h) Ξ(h⁻¹ g) (1 + σ(h))^s dμ(h) = Ξ(g) ∫_G Ξ(h)² (1 + σ(h))^s dμ(h)`, as
  integrals in `ℝ≥0∞`. This is the `K`-averaging step of the proof.
- `ConvolutionWeights.lintegral_enorm_mul_le` (`r ≥ 0`, any `r'`):
  `∫_G |f₁(h) f₂(h⁻¹ g)| dμ(h) ≤ ν_{r'}(f₁) ν_r(f₂) Ξ(g) (1 + σ(g))^{-r}
  ∫_G Ξ(h)² (1 + σ(h))^{r - r'} dμ(h)`, the third display of Waldspurger's proof.
- `ConvolutionWeights.nu_convolution_le` (`r ≥ 0`, any `r'`):
  `ν_r(f₁ * f₂) ≤ ν_{r'}(f₁) ν_r(f₂) ∫_G Ξ(h)² (1 + σ(h))^{r - r'} dμ(h)`.
- `ConvolutionWeights.nu_convolution_le_square` (`r ≥ 0`) and
  `ConvolutionWeights.nu_convolution_le_max` (any `r`, with `r₀ = max r 0`):
  `ν_r(f₁ * f₂) ≤ c ν_{r₀ + d}(f₁) ν_{r₀}(f₂)` with `d = squareExponent` and
  `c = ∫_G Ξ(h)² (1 + σ(h))^{-d} dμ(h) < ∞`. This is the estimate
  `ν_r(f₁ * f₂) ≤ c ν_{r'}(f₁) ν_r(f₂)` at the end of Waldspurger's proof.
- `ConvolutionWeights.integrable_mul`: if `f₁` and `f₂` are continuous with
  `ν_d(f₁) < ∞` and `ν_0(f₂) < ∞`, then `h ↦ f₁(h) f₂(h⁻¹ g)` is integrable for every
  `g`.
- `continuous_of_mem_levelSubmodule` (topological group only): elements of a level
  `C_H` are continuous.
- `ConvolutionWeights.integrable_mul_of_mem`: for `f₁ ∈ C_{H₁}` and `f₂ ∈ C_{H₂}`,
  the convolution integrand is integrable for every `g`.
- `ConvolutionWeights.convolution_mem_levelSubmodule`: `C_H` is stable under
  convolution.
- `Level.continuous_of_nu_le` (no measure or weight hypotheses): a linear map
  `T : C_{H₁} → C_{H₂}` is continuous if for every `r` there are `s` and a finite `C`
  with `ν_r(T f) ≤ C ν_s(f)` for all `f`.
- `Level.continuous_convolutionLeft`, `Level.continuous_convolutionRight`: the maps
  `Level.convolutionLeft` and `Level.convolutionRight` are continuous.

The following results also assume that `G` has a compact open subgroup
(`Nonempty (CompactOpenSubgroup G)`), so that `C(G)` is the union of its levels:

- `ConvolutionWeights.integrable_mul_of_mem_schwartzSubmodule`: for `f₁, f₂ ∈ C(G)` the
  convolution integral converges absolutely for every `g` (first assertion of
  Lemma III.6.1).
- `ConvolutionWeights.convolution_mem_schwartzSubmodule`: `f₁ * f₂ ∈ C(G)` (second
  assertion).
- `Space.coe_convolution`, `Space.convolutionBilin_apply`: the product on `C(G)` is
  the function `convolution μ f₁ f₂`.
- `Space.continuous_convolution_left`, `Space.continuous_convolution_right`: for fixed
  `f₂`, `f₁ ↦ f₁ * f₂` is continuous on `C(G)`, and for fixed `f₁`, `f₂ ↦ f₁ * f₂` is
  continuous on `C(G)` (third assertion: separate continuity).

## Proof notes

The Lean proof follows Waldspurger's.

1. Pointwise bound. `|f(g)| ≤ ν_r(f) Ξ(g) (1 + σ(g))^{-r}`, together with
   `1 + σ(g) ≤ (1 + σ(h)) (1 + σ(h⁻¹ g))` raised to the power `-r ≤ 0`, gives
   `enorm_mul_le`.
2. `K`-averaging (`lintegral_xi_mul_xi`). For `k ∈ K`, left invariance of `μ` replaces
   `h` by `k⁻¹ h` (`lintegral_mul_left_eq_self`). Left `K`-invariance of `Ξ` and `σ`
   turns the integrand into `Ξ(h) (1 + σ(h))^s Ξ(h⁻¹ k g)`. Since the left side does
   not depend on `k` and `K` has measure one, the integral equals its average over `K`.
   Tonelli's theorem (`lintegral_lintegral_swap`; the integrand is continuous on
   `K × G`, hence measurable because `G` is second countable) exchanges the integrals.
   The inner integral over `K` is `Ξ(h⁻¹) Ξ(g) = Ξ(h) Ξ(g)` by `integral_xi` and
   `xi_inv`. Waldspurger replaces `h` by `kh`; the Lean proof uses `k⁻¹ h`, which gives
   the same average.
3. Integrating the pointwise bound and applying step 2 gives
   `lintegral_enorm_mul_le`. Taking the supremum over `g` after multiplying by
   `Ξ(g)⁻¹ (1 + σ(g))^r` gives `nu_convolution_le`. With `r' = r + d`, the remaining
   integral is finite by `square`.
4. Levels. Elements of `C_H` are bi-invariant under the compact open subgroup `H`,
   hence locally constant and continuous, so step 3 gives absolute convergence and
   `ν_r(f₁ * f₂) < ∞` for all `r`. Bi-invariance of `f₁ * f₂` uses left invariance of
   `μ`. For `f₁ ∈ C_{H₁}` and `f₂ ∈ C_{H₂}` both lie in `C_{H₁ ∩ H₂}`.
5. Continuity. On levels, `nu_convolution_le_max` bounds each seminorm of the image by a
   finite multiple of a seminorm of the argument, which gives continuity of
   `Level.convolutionLeft` and `Level.convolutionRight`. Waldspurger reduces the
   continuity on `C(G)` to the levels by III.6(1). The Lean proof does the same with
   `Space.continuous_iff_continuous_comp` from `Basic`: for fixed `f₂ ∈ C_{H₂}`, the
   restriction of `f₁ ↦ f₁ * f₂` to `C_{H₁}` is the inclusion of `C_{H₁ ∩ H₂}` composed
   with `Level.convolutionLeft`, and similarly in the second variable.
