# `π(f₁ ∗ f₂) = π(f₁) π(f₂)` on `C(G)` and translations (III.7)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzActionConvolution`,
namespace `Langlands.HarishChandraSchwartz`. It imports `SchwartzAction` (`schwartzAction`,
`schwartzAction_eval`, `HasTemperedCoefficients`, `exists_nu_coefficient_ne_top`,
`continuous_coefficient`, `ext_smoothDual`), `Convolution` (`ConvolutionWeights`,
`convolution`, `convolution_apply`, `Space.convolution`, `lintegral_enorm_mul_le`,
`squareExponent`, `lintegral_square_lt_top`, `enorm_le_nu_mul`) and `Translations`
(`TranslationWeights`, `Space.translate`, `Space.translate_apply`); through them `Basic`
(`Space`, `nu`, `nu_mono`, `mem_schwartzSubmodule_iff`) and `L2` (`L2Weights`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

- III.7 (printed p. 273, PDF p. 39), first paragraph: "Remarquons que si
  `ϕ ∈ C^w_lisse(G)` et `f ∈ C(G)`, l'intégrale `∫_G f(g)ϕ(g) dg` est absolument
  convergente [...]. La preuve est identique à celle du Lemme III.6.1 où l'on choisit
  `r ∈ ℝ` tel que `ν_r(ϕ)` soit fini." Then, after the definition of `π(f)` (formalized in
  `SchwartzAction`): "On vérifie que `π(f_1 ∗ f_2) = π(f_1)π(f_2)` pour tous
  `f_1, f_2 ∈ C(G)`."
- III.6 (printed pp. 271–272, PDF pp. 37–38) and Lemma III.6.1: the convolution
  `(f_1 ∗ f_2)(g) = ∫_G f_1(h) f_2(h⁻¹ g) dh` on `C(G)` (formalized in `Convolution`).
- I.6 (printed p. 249, PDF p. 15): `G` acts on functions by right and left translations.

The two translation formulas `schwartzAction_translate_left` and
`schwartzAction_translate_right` are not stated in the source; they are derived here
(standard consequences of the definition of `π(f)` and invariance of the measure), with the
explicit translates `x ↦ f(a⁻¹ x)` and `x ↦ f(x a)` of `Space.translate`.

## Scope: abstract data and explicit hypotheses

As in `SchwartzAction`, `G` is a topological group with a compact open subgroup
(`[Nonempty (CompactOpenSubgroup G)]`), `μ` is a left invariant measure
(`[μ.IsMulLeftInvariant]`), the weights `Ξ, σ : G → ℝ` are arbitrary, and the
representation `ρ : Representation ℂ G V` carries the hypotheses `hρ : IsAdmissible ρ` and
`hT : HasTemperedCoefficients Ξ σ ρ`; `π(f)` is `schwartzAction hw hρ hT f` with
`hw : L2Weights μ Ξ σ`. Nothing is proved here about Waldspurger's own `Ξ`, `σ` or Haar
measure. The hypotheses of each result are:

- `ConvolutionWeights.lintegral_lintegral_enorm_mul_lt_top`,
  `ConvolutionWeights.integrable_prod`, `ConvolutionWeights.integral_convolution_mul`:
  `[IsTopologicalGroup G] [BorelSpace G] [SecondCountableTopology G]`, `[SFinite μ]`,
  `[μ.IsMulLeftInvariant]`, a subgroup `K` with `[CompactSpace K]` and
  `hw : ConvolutionWeights μ K Ξ σ` (the weight hypotheses of Lemma III.6.1, see
  `Convolution`); `f₁, f₂ : G → ℂ` with `ν_r(f_i) ≠ ∞` for every `r`, and `φ : G → ℂ` with
  `ν_s(φ) ≠ ∞` for one `s`. The last two results also assume `f₁`, `f₂`, `φ` continuous.
- `Space.forall_nu_ne_top`: `[IsTopologicalGroup G] [Nonempty (CompactOpenSubgroup G)]`.
- `eval_rho_schwartzAction` and `schwartzAction_translate_left`: the hypotheses of
  `SchwartzAction` (`[OpensMeasurableSpace G] [MeasurableMul G]`, `[μ.IsMulLeftInvariant]`,
  `hw`, `hρ`, `hT`); `schwartzAction_translate_left` adds
  `ht : TranslationWeights Ξ σ` (needed for `Space.translate` to map `C(G)` to itself).
- `schwartzAction_convolution`: `[BorelSpace G] [SecondCountableTopology G]`, `[SFinite μ]`,
  `[μ.IsMulLeftInvariant]`, `hw : L2Weights μ Ξ σ`, a compact subgroup `K` with
  `hc : ConvolutionWeights μ K Ξ σ` (for `Space.convolution hc`), `hρ` and `hT`.
- `schwartzAction_translate_right`: as `schwartzAction_translate_left`, and in addition
  `[μ.IsMulRightInvariant]`. Waldspurger's `G` is unimodular, so his Haar measure is right
  invariant; this is not proved here.

## Definition

- `convolutionIntegrand f₁ f₂ φ : G × G → ℂ` is `(h, g) ↦ f₁(h) f₂(h⁻¹ g) φ(g)`, the
  integrand of the double integral `∫_G ∫_G f₁(h) f₂(h⁻¹ g) φ(g) dh dg` whose inner integral
  over `h` is `(f₁ ∗ f₂)(g) φ(g)` (`convolutionIntegrand_apply` unfolds it). It is a helper
  introduced for this proof, not a notion named in the source.

## Results

- `ConvolutionWeights.lintegral_lintegral_enorm_mul_lt_top`:
  `∫_G (∫_G |f₁(h)| |f₂(h⁻¹ g)| dμ(h)) |φ(g)| dμ(g) < ∞`.
- `ConvolutionWeights.integrable_prod`: `convolutionIntegrand f₁ f₂ φ` is integrable for
  `μ × μ` on `G × G`.
- `ConvolutionWeights.integral_convolution_mul`:
  `∫_G (f₁ ∗ f₂)(g) φ(g) dμ(g) = ∫_G f₁(h) ∫_G f₂(y) φ(h y) dμ(y) dμ(h)`, with `f₁ ∗ f₂`
  the function `convolution μ f₁ f₂`.
- `Space.forall_nu_ne_top`: every `f ∈ C(G)` has `ν_r(f) ≠ ∞` for all `r`.
- `eval_rho_schwartzAction`:
  `ℓ(ρ(h) π(f) v) = ∫_G f(y) ℓ(ρ(h y) v) dμ(y)` for every smooth functional `ℓ`.
- `schwartzAction_convolution` (III.7): for `f₁, f₂ ∈ C(G)`,
  `π(Space.convolution hc f₁ f₂) = π(f₁) π(f₂)` as endomorphisms of `V`.
- `schwartzAction_translate_left`: `π(Space.translate ht 1 a f) = ρ(a) π(f)`, where
  `Space.translate ht 1 a f` is `x ↦ f(a⁻¹ x)`.
- `schwartzAction_translate_right`: `π(Space.translate ht a 1 f) = π(f) ρ(a⁻¹)`, where
  `Space.translate ht a 1 f` is `x ↦ f(x a)`.

## Proof notes

Absolute convergence follows the proof of Lemma III.6.1 as the source indicates. Let `d` be
the exponent of Lemma II.1.5 in `ConvolutionWeights` (`squareExponent`), `s' = min(s, d)`
(so `ν_{s'}(φ) ≤ ν_s(φ)` by `nu_mono`) and `r = d - s' ≥ 0`. The estimate
`lintegral_enorm_mul_le` of `Convolution` with exponents `r` and `r + d` gives
`∫ |f₁(h)| |f₂(h⁻¹ g)| dh ≤ ν_{r+d}(f₁) ν_r(f₂) Ξ(g)(1 + σ(g))^{-r} ∫ Ξ²(1 + σ)^{-d}`, and
`|φ(g)| ≤ ν_{s'}(φ) Ξ(g)(1 + σ(g))^{-s'}`. The product is a constant times
`Ξ(g)²(1 + σ(g))^{-d}`, whose integral is finite. Tonelli (`lintegral_prod_symm`) turns this
into integrability of the continuous function `(h, g) ↦ f₁(h) f₂(h⁻¹ g) φ(g)` on `G × G`.

Fubini (`integral_integral_swap`) then exchanges the two integrals in
`∫_g ∫_h f₁(h) f₂(h⁻¹ g) φ(g)`, and in the inner integral the left invariance of `μ`
(`integral_mul_left_eq_self`) substitutes `g = h y`.

For `schwartzAction_convolution`, both sides are compared by pairing with smooth functionals
(`ext_smoothDual`). By `schwartzAction_eval`, `ℓ(π(f₁ ∗ f₂) v) = ∫ (f₁ ∗ f₂)(g) ℓ(ρ(g) v)`
and `ℓ(π(f₁) π(f₂) v) = ∫ f₁(h) ℓ(ρ(h) π(f₂) v) dh`; by `eval_rho_schwartzAction` the inner
term is `∫ f₂(y) ℓ(ρ(h y) v) dy`. The coefficient `φ(g) = ℓ(ρ(g) v)` is continuous
(`continuous_coefficient`) with some `ν_s(φ)` finite (`exists_nu_coefficient_ne_top`), so
`integral_convolution_mul` applies.

`eval_rho_schwartzAction` writes `ℓ ∘ ρ(h)` as the smooth functional
`smoothContragredient ρ h⁻¹ ℓ` and applies `schwartzAction_eval`. The translation formulas
follow from `schwartzAction_eval` and the substitution `x ↦ a x` (left invariance, via
`integral_mul_left_eq_self`) respectively `x ↦ x a⁻¹` (right invariance, via
`integral_mul_right_eq_self`), again by separation with smooth functionals.

## Relation to the Library

`Hecke.integratedAction_convolution` (`Langlands.Representation.Hecke.IntegratedConvolution`)
is the analogous identity for the integrated action of test functions (`SchwartzBruhat G`,
compactly supported) on a smooth representation, proved with compact-support Fubini. The
present module covers `C(G)`, whose elements need not have compact support, by the weighted
estimate above; `schwartzAction_ofSchwartzBruhat` of `SchwartzAction` identifies the two
actions on test functions.

## Open obligations

This module does not treat the other statements of III.7: that `f ϕ ∈ C(G)` for
`f ∈ A(ω)`, `ω` square integrable, and `ϕ ∈ C_c(G/G^1)` (from Corollary III.1.2; the subject
of the separately submitted module `CoefficientCutoff`, not imported here), and
Proposition III.7.1 (the operators `π(p)`), which remains open.
