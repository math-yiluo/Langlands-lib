# Theta series on the fundamental cone: convergence, decay and theta data

Module `Langlands.Global.Hecke.ThetaDecay`, namespace `Langlands.Global.Hecke`.

Throughout, `K` is a number field, `V = mixedSpace K = (ℝ^{real places}) × (ℂ^{complex places})`
is its mixed space with the componentwise ring structure, the sup norm
`‖x‖ = max_w normAtPlace w x` and Lebesgue measure `volume`,
`N = mixedEmbedding.norm : V → ℝ` is the norm `N(x) = ∏_w ‖x_w‖^{mult w}`,
`C = fundamentalCone K` is Mathlib's fundamental cone for the unit action, `n = [K : ℚ]`, and
`𝒟 = fundamentalDyadicCone` is `C` with `N` viewed as a dyadic cone (from
`Langlands.Global.Hecke.MixedSpaceUnfolding`), with `𝒟.lower = {x ∈ C | N x ≤ 1}`,
`𝒟.upper = {x ∈ C | 1 < N x}` and `𝒟.piece 0` its first dyadic shell. Fractional ideals are
units `I : (FractionalIdeal (𝓞 K)⁰ K)ˣ`, and `idealLattice K I ⊆ V` is the image of `I` under
the mixed embedding.

This module supplies the analytic input of the dyadic-cone Mellin functional equation of
`Langlands.Global.Hecke.ConeMellin` for theta series over fractional ideals: absolute
convergence, Gaussian decay of the non-constant part at the top and at the bottom of the
fundamental cone, measurability and integrability, and finally the construction of a
`DyadicCone.ThetaData` structure (`coneThetaData`) from a Poisson summation relation. It is an
internal helper for the proof of the Hecke global functional equation; it states nothing about
`L`-functions.

## Provenance

Internal. The facts are the standard estimates of Hecke's proof of the functional equation
(theta series over a lattice converge absolutely and their non-constant part decays
exponentially; Tate's thesis replaces them by the corresponding estimates on the idele class
group). Here they are derived directly from a Gaussian bound
`|F(z)| ≤ C e^{-c ‖z‖²}`, from the discreteness of the ideal lattice, and from the comparison
`normAtPlace w x ≍ N(x)^{1/n}` on the fundamental cone (`exists_normAtPlace_bounds`, proved in
`Langlands.Global.Hecke.MixedSpaceUnfolding`). The form of the statements (one summable
majorant, explicit decay rates, the `ThetaData` fields) is chosen for the internal assembly and
is not taken from the literature.

## Definitions

- `toIdealLattice I : (I : Set K) → idealLattice K I`, `γ ↦ mixedEmbedding K γ`; it is
  injective (`toIdealLattice_injective`).
- `thetaSeries a F y = ∑' γ : K, a γ * F (mixedEmbedding K γ * y)` for `a : K → ℂ`,
  `F : V → ℂ`, `y : V` (the theta series `θ(a, F)(y) = ∑_{γ ∈ K} a(γ) F(γ y)`; `tsum`, so it
  is `0` where the family is not summable).
- `coneThetaData I J ha hb ha_bdd hb_bdd hFc hGc hF hG hχm hχb hpoisson hl hχ2 :
  fundamentalDyadicCone.ThetaData volume`, see below.

## Main results

Elementary bounds:

- `rpow_le_one_add_rpow_abs`: for `u ≥ 1` and real `a`, `u^a ≤ (1 + u)^{|a|}`.
- `exists_exp_neg_mul_sq_mul_rpow_le`: for `c > 0` and real `a, r` there is `C > 0` with
  `e^{-c u²} u^a ≤ C (1 + u)^{-r}` for all `u ≥ 1`.
- `exists_pos_le_norm_of_mem`: a discrete `ℤ`-submodule `L` of a normed group has `δ > 0` with
  `δ ≤ ‖x‖` for every nonzero `x ∈ L`.
- `norm_le_of_normAtPlace_le`: if `normAtPlace w x ≤ R` for all `w`, then `‖x‖ ≤ R`.
- `mul_norm_le_norm_mul`: if `m ≤ normAtPlace w y` for all `w`, then `m ‖z‖ ≤ ‖z * y‖` for all
  `z : V`.
- `summable_indicator_exp_neg_mul_sq`: for `c > 0`, `γ ↦ 1_I(γ) e^{-c ‖γ‖²}` (with
  `‖γ‖ = ‖mixedEmbedding K γ‖`) is summable over `K`.

Convergence and decay. In the following, `a : K → ℂ` satisfies `a γ ≠ 0 → γ ∈ I` and
`‖a γ‖ ≤ M` for all `γ`, and `F : V → ℂ` satisfies `‖F z‖ ≤ C e^{-c ‖z‖²}` with `c > 0`.

- `exists_thetaSeries_decay`: for `m₀ > 0` there are `u : K → ℝ` summable, `D ≥ 0` and
  `c' > 0` such that `‖a γ * F (γ y)‖ ≤ u γ` for every `γ` and every `y` with
  `m₀ ≤ normAtPlace w y` for all `w`, and
  `‖θ(a, F)(y) - a(0) F(0)‖ ≤ D e^{-c' m²}` whenever `m₀ ≤ m` and `m ≤ normAtPlace w y` for
  all `w`.
- `exists_thetaSeries_decay_cone`: there are `u` summable, `D ≥ 0`, `c' > 0` such that for
  every `x ∈ C` with `N x ≥ 1`, `‖a γ * F (γ x)‖ ≤ u γ` for all `γ` and
  `‖θ(a, F)(x) - a(0) F(0)‖ ≤ D e^{-c' (N(x)^{1/n})²}`.
- `exists_thetaSeries_inv_decay_cone`: there are `u` summable, `D ≥ 0`, `c' > 0` such that for
  every `x ∈ C` with `N x ≤ 1`, `‖a γ * F (γ x⁻¹)‖ ≤ u γ` for all `γ` and
  `‖θ(a, F)(x⁻¹) - a(0) F(0)‖ ≤ D e^{-c' ((N(x)^{1/n})⁻¹)²}`.
- `continuousOn_tsum_theta`: if `F` is continuous, `φ : V → V` is continuous on `s` and the
  terms `‖a γ * F (γ φ(y))‖` are bounded by a summable `u γ` for `y ∈ s`, then
  `y ↦ θ(a, F)(φ y)` is continuous on `s`.

Integrability on the cone (`χ : V → ℂ` with `‖χ x‖ ≤ Kχ N(x)^τ` on `C`):

- `norm_rpow_eq_rpow_root`: for `x ∈ C`, `N(x)^a = (N(x)^{1/n})^{n a}`.
- `volume_lower_lt_top`: `volume 𝒟.lower < ∞`.
- `integrableOn_upper_of_decay`: if `f χ` is a.e. strongly measurable on `𝒟.upper`, and
  `‖f x‖ ≤ D e^{-c' (N(x)^{1/n})²}` for `x ∈ C`, `N x ≥ 1` (`D ≥ 0`, `c' > 0`), then
  `x ↦ ‖f x * χ x‖ * N(x)^σ` is integrable on `𝒟.upper` for every real `σ`.
- `integrableOn_lower_of_decay`: likewise on `𝒟.lower` if
  `‖g x‖ ≤ D e^{-c' ((N(x)^{1/n})⁻¹)²}` for `x ∈ C`, `N x ≤ 1`.
- `integrableOn_piece_zero_of_bound`: if `χ` is a.e. strongly measurable on `C`, then `χ` is
  integrable on `𝒟.piece 0`.
- `continuousOn_inv_lower`: `x ↦ x⁻¹` is continuous on `𝒟.lower`.

Theta data. Let `a`, `b : K → ℂ` be bounded with `a γ ≠ 0 → γ ∈ I` and `b γ ≠ 0 → γ ∈ J`,
let `F`, `G : V → ℂ` be continuous with Gaussian bounds `‖F z‖ ≤ C e^{-c ‖z‖²}` (some `C`,
`c > 0`, and likewise for `G`), and let `χ : V → ℂ` be a.e. strongly measurable on `C` with
`‖χ x‖ ≤ Kχ N(x)^τ` on `C` for some `Kχ, τ`.

- `aestronglyMeasurable_thetaSeries_upper`: `x ↦ (θ(a, F)(x) - a(0) F(0)) χ(x)` is a.e.
  strongly measurable on `𝒟.upper`;
  `aestronglyMeasurable_thetaSeries_lower`: `x ↦ (θ(b, G)(x⁻¹) - b(0) G(0)) χ(x)` is a.e.
  strongly measurable on `𝒟.lower`.
- `integrableOn_thetaSeries_upper`, `integrableOn_thetaSeries_lower`: for every real `σ`,
  `‖(θ(a, F)(x) - a(0) F(0)) χ(x)‖ N(x)^σ` is integrable on `𝒟.upper`, and
  `‖(θ(b, G)(x⁻¹) - b(0) G(0)) χ(x)‖ N(x)^σ` is integrable on `𝒟.lower`.
- `coneThetaData`: given in addition the Poisson relation
  `θ(a, F)(x) = N(x)⁻¹ θ(b, G)(x⁻¹)` for `x ∈ C` (`hpoisson`), a nonzero `l : ℂ` and
  `χ(2 • x) = l χ(x)` for `x ∈ C`, the `ThetaData` structure on `𝒟` for `volume` with weight
  `χ`, multiplier `l`, `f(x) = θ(a, F)(x) - a(0) F(0)`, `g(x) = θ(b, G)(x⁻¹) - b(0) G(0)`,
  `A = a(0) F(0)` and `B = b(0) G(0)`. Its relation field `f x + A = N(x)⁻¹ (g x + B)` is
  exactly `hpoisson`.

## Proofs

**Elementary bounds.** `rpow_le_one_add_rpow_abs`: for `a ≥ 0` use monotonicity of
`t ↦ t^a`; for `a ≤ 0`, `u^a ≤ 1 ≤ (1 + u)^{|a|}`. `exists_exp_neg_mul_sq_mul_rpow_le` applies
`exists_exp_neg_mul_sq_le_rpow` (from `MixedSpaceFourier`) with exponent `r + |a|` and
multiplies by the previous bound. `exists_pos_le_norm_of_mem`: `{0}` is open in the discrete
subspace `L`, so a ball of some radius `ε` around `0` in `L` is `{0}`
(`Metric.isOpen_singleton_iff`). `mul_norm_le_norm_mul`: choose the place `w` where
`‖z‖ = normAtPlace w z`; then `m ‖z‖ ≤ normAtPlace w y · normAtPlace w z = normAtPlace w (z y)
≤ ‖z y‖`.

**Gaussian sums over ideals.** By `exists_exp_neg_mul_sq_le_rpow`, `e^{-c ‖v‖²}` is bounded by
`C (1 + ‖v‖)^{-(dim V + 1)}`, so `summable_add_zlattice_of_decay` (from
`LatticePoissonGeneral`; Mathlib provides the `DiscreteTopology` and `IsZLattice` instances of
`idealLattice K I`) gives summability over the lattice. Composition with the injective map
`toIdealLattice I` gives summability over the subtype `I ⊆ K`, which is the summability of the
indicator function (`summable_subtype_iff_indicator`).

**Decay (`exists_thetaSeries_decay`).** Let
`g(γ) = 1_I(γ) e^{-c m₀² ‖γ‖²}`, summable by the previous step. If all coordinates of `y` are
at least `m₀`, then `‖γ y‖ ≥ m₀ ‖γ‖` (`mul_norm_le_norm_mul`), so for `γ ∈ I`
`‖a γ F(γ y)‖ ≤ M C e^{-c ‖γ y‖²} ≤ M C g(γ)`, and the term vanishes for `γ ∉ I`; this is the
majorant `u = M C g`. (`C ≥ 0` and `M ≥ 0` follow from the bounds at `0`.) For the decay, split
off the term `γ = 0` (`tsum_eq_add_tsum_ite`), which is `a(0) F(0)`. Let `δ > 0` be the minimal
norm of the nonzero vectors of `idealLattice K I` (`exists_pos_le_norm_of_mem`). For
`0 ≠ γ ∈ I`, with `A = ‖γ‖ ≥ δ` and `B = ‖γ y‖ ≥ m A`,
`B² ≥ m² A² ≥ m₀² A² + δ² m² - m₀² δ²` (because `(m² - m₀²)(A² - δ²) ≥ 0`), so
`e^{-c B²} ≤ e^{c m₀² δ²} e^{-c δ² m²} e^{-c m₀² A²}`. Summing,
`‖θ(a, F)(y) - a(0) F(0)‖ ≤ M C e^{c m₀² δ²} (∑ g) · e^{-c δ² m²}`
(`tsum_of_norm_bounded`); this is the claim with `D = M C e^{c m₀² δ²} ∑ g` and `c' = c δ²`.

**Decay on the cone.** Let `r, R > 0` be the constants of `exists_normAtPlace_bounds`, so that
`r t ≤ normAtPlace w x ≤ R t` for `x ∈ C`, `t = N(x)^{1/n}`. At the top (`N x ≥ 1`, so
`t ≥ 1`), apply `exists_thetaSeries_decay` with `m₀ = r` and `m = r t`; the decay rate becomes
`c' r²`. At the bottom (`N x ≤ 1`, so `t ≤ 1`), the coordinates of `x⁻¹` are
`(normAtPlace w x)⁻¹ ≥ R⁻¹ t⁻¹ ≥ R⁻¹` (`normAtPlace_inv`); apply `exists_thetaSeries_decay` at
`x⁻¹` with `m₀ = R⁻¹` and `m = R⁻¹ t⁻¹`; the decay rate becomes `c' R⁻²`.

**Continuity.** `continuousOn_tsum_theta` is `continuousOn_tsum` (Weierstrass M-test): each
term `y ↦ a γ F(γ φ(y))` is continuous on `s`, and the terms are dominated by the summable `u`.

**Integrability.** At the top, for `x ∈ 𝒟.upper` with `t = N(x)^{1/n} ≥ 1`:
`‖χ x‖ N(x)^σ ≤ |Kχ| N(x)^{τ + σ} = |Kχ| t^{n(τ+σ)}` (`norm_rpow_eq_rpow_root`), so
`‖f x χ x‖ N(x)^σ ≤ D |Kχ| e^{-c' t²} t^{n(τ+σ)} ≤ D |Kχ| C₁ (1 + t)^{-(dim V + 1)}` by
`exists_exp_neg_mul_sq_mul_rpow_le`. Since `‖x‖ ≤ R t` (`norm_le_of_normAtPlace_le`), we have
`1 + ‖x‖ ≤ (1 + R)(1 + t)`, hence `(1 + t)^{-(d+1)} ≤ (1 + R)^{d+1} (1 + ‖x‖)^{-(d+1)}`
(`rpow_neg_le_of_le_mul` from `LatticePoissonGeneral`), and `(1 + ‖x‖)^{-(d+1)}` is integrable on
`V` (`integrable_one_add_norm`, `d = dim V`). `Integrable.mono'` concludes, with the measurability
of `‖f χ‖ N^σ` from the hypothesis and the measurability of `N`. At the bottom,
`𝒟.lower` is bounded (`fundamentalCone.isBounded_normLeOne`), so has finite measure, and with
`s = t⁻¹ ≥ 1`, `‖χ x‖ N(x)^σ ≤ |Kχ| s^{-n(τ+σ)}` and
`e^{-c' s²} s^{-n(τ+σ)} ≤ C₂` (`exists_exp_neg_mul_sq_mul_rpow_le` with `r = 0`), so the
integrand is bounded by a constant on a set of finite measure. On the first shell,
`𝒟.piece 0 ⊆ 𝒟.lower` (`level_nonpos_iff`) and
`N(x)^τ ≤ e^{|τ| dim V log 2}` there (`rpow_le_of_mem_piece_zero` from `ConeMellin`), so `χ`
is again bounded on a set of finite measure. `continuousOn_inv_lower`: `x ↦ x⁻¹` is
differentiable at every `x` with `N x ≠ 0` (`hasFDerivAt_inv'` from `MixedSpaceUnfolding`),
and `N > 0` on `C`.

**Theta data.** Measurability: by `exists_thetaSeries_decay_cone` (resp.
`exists_thetaSeries_inv_decay_cone`) and `continuousOn_tsum_theta` (with `φ = id`, resp.
`φ(x) = x⁻¹` and `continuousOn_inv_lower`), `θ(a, F)` is continuous on `𝒟.upper` and
`x ↦ θ(b, G)(x⁻¹)` is continuous on `𝒟.lower`, hence a.e. strongly measurable on these
measurable sets (`ContinuousOn.aestronglyMeasurable`); multiply by the restriction of the
measurability of `χ` on `C`. Integrability is `integrableOn_upper_of_decay` and
`integrableOn_lower_of_decay` with the decay bounds of the two cone lemmas. In
`coneThetaData`, the fields `χ_two_smul` and `l_ne_zero` are the hypotheses, `integrableOn_χ`
is `integrableOn_piece_zero_of_bound`, `f_add` reduces to `hpoisson` after `sub_add_cancel`,
and the measurability and integrability fields are the four lemmas above.
