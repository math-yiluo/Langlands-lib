# Reduction of the unequal-rank gauge premises to Whittaker gauge bounds

Module `Langlands.Global.RankinSelberg.UnequalGaugeReduction`, namespace
`Langlands.Global.RankinSelbergGlobal`.

`UnequalGaugeReductionStatement` is a Prop-valued statement. It says that
two gauge bounds involving only the Whittaker function of the larger
group, `UnequalPadGaugeStatement` and `UnequalRectGaugeStatement`, imply
the Library statement `UnequalUnfoldingGaugeStatement`. That Library
statement asserts the premises `WhittakerGaugeIntegrable` (G) and
`DualWhittakerGaugeIntegrable` (G') of `UnequalUnfoldingReductionStatement`
for every actual unequal-rank cuspidal pair. The module also proves the
reduction: `unequalGaugeReduction : UnequalGaugeReductionStatement`.

The two new statements are still open. This module does not prove
`UnequalUnfoldingGaugeStatement`. It removes the cusp form `φ'` of the
smaller group from G and G', leaving estimates about `W_φ` alone.

Provenance: derived. Sources: Cogdell, *Analytic theory of L-functions for
GL_n* (2004), §2.2, printed pp.206–207 (PDF pp.209–210), source
`cogdell-2004-analytic-theory-gln`. On p.206 Cogdell says the ordinary
integral "is absolutely convergent for Re(s) » 0 by the gauge estimates
of [22, Section 13]". He then integrates over `N_m(k)\N_m(𝔸)` and obtains
`Ψ(s; W_φ, W'_φ')` over `N_m(𝔸) \ GL_m(𝔸)`, and "we retain absolute
convergence for Re(s) » 0". On p.207, "As before, Ψ̃(s; W, W') is
absolutely convergent for Re(s) » 0". In that integral the
`x`-integral runs over `M_{n-m-1,m}(𝔸)` and the `h`-integral over
`N_m(𝔸) \ GL_m(𝔸)`. The two statements below are these convergence
claims with the factor of the smaller group (`W'` or `φ'`) replaced by a
power of `|det h|`. They are the form the gauge estimates take once that
factor is bounded. The exponent bound `C` is uniform over standard
characters and vectors because the target premises require that
uniformity. Cogdell states convergence for each fixed datum.

## Notation

`n = r + 1`, `m = t + 1`, `W = cuspWhittaker F T ψ v`, `W̃ = dualFunction F n W`
(the Library's `g ↦ W(w ᵗg⁻¹)`), `w' = unfoldingWeyl F h`, `rect` for
`rectangularPoint F h`, `pad` for
`pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) : Points F m → Points F n`
(`h ↦ diag(h, I_{n-m})`), and `|det g|` for `detNorm F m g`. "Standard"
means `IsStandardAdditiveCharacter F ψ`. The space `N_m(𝔸) \ GL_m(𝔸)` is
`WhittakerQuotient F m` with the Library's `whittakerQuotientMeasure F m`.
Functions on it are evaluated at the quotient representatives `p.out`.
The rectangular matrices `M_{(n-m-1)×m}(𝔸)` carry
`rectangleMeasure F (r - (t + 1)) (t + 1)`. All integrals are lower
(`ℝ≥0∞`-valued) integrals of norms, so finiteness means absolute
convergence.

## The statements

1. `PadWhittakerGaugeBound F h T` (for `h : t < r` and
   `T : CuspidalOperatorRealization F r`): there is `C : ℝ` with `0 ≤ C`
   such that for every standard `ψ`, every `v : T.Space` and every real
   `σ > C`,

   `∫⁻ p, ‖W(pad p.out)‖ₑ · ofReal(|det p.out|^σ) ∂whittakerQuotientMeasure F m < ⊤`.

2. `RectWhittakerGaugeBound F h T`: there is `C : ℝ` with `0 ≤ C` such
   that for every standard `ψ`, every `v` and every real `σ > C`,

   `∫⁻ p, (∫⁻ x, ‖translateFunction F n w' W̃ (rect(p.out, x))‖ₑ ∂rectangleMeasure)
      · ofReal(|det p.out|^σ) ∂whittakerQuotientMeasure F m < ⊤`.

   Here `translateFunction F n w' W̃ (g) = W̃(g w')`.

3. `UnequalPadGaugeStatement.{u}`: for every `F : Type u` with
   `[Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]`, all
   `r t : ℕ`, `h : t < r` and `T : CuspidalOperatorRealization F r`,
   `PadWhittakerGaugeBound F h T`.

4. `UnequalRectGaugeStatement.{u}`: the same quantifiers, with
   `RectWhittakerGaugeBound F h T`.

5. `UnequalGaugeReductionStatement.{u}` is

   `UnequalPadGaugeStatement.{u} → UnequalRectGaugeStatement.{u} →
     UnequalUnfoldingGaugeStatement.{u}`.

The cuspidal realization `T'` of the smaller group does not appear in
statements 1–4.

## Proof

Namespace `GaugeReduction`:

- `norm_detPower_eq_rpow`: `‖detPower F n g z‖ = detNorm F n g ^ z.re`
  (from `UnequalAnalytic.norm_detPower`). `re_unfolding_exponent` computes
  `(s - k/2).re = s.re - k/2`.
- `detNorm_unipotent_mul`: `|det|` is left `N_m(𝔸)`-invariant.
- `lintegral_rationalQuotient_eq`: suppose `M : Points F m → ℝ≥0∞` is
  measurable and left `N_m(𝔸)`-invariant. Then its lower integral at
  representatives over `N_m(F) \ GL_m(𝔸)`
  (`LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F m) _`)
  equals its lower integral at representatives over `WhittakerQuotient F m`
  for `whittakerQuotientMeasure F m`. The proof unfolds
  `whittakerQuotientMeasure` as the pushforward of the rational
  quotient measure (`lintegral_map`). The representative of the image of
  `q` is an `N_m(𝔸)`-translate of `q.out` (`exists_out_mk_eq`), so the
  two integrands agree.
- `norm_cuspWhittaker_pad_unipotent_mul`: `|W(pad(n x))| = |W(pad x)|` for
  `n ∈ N_m(𝔸)`, since `pad n ∈ N_n(𝔸)` and the generic character has norm one.
- `whittakerGaugeIntegrable_of_pad` (premise G). Take `β` from
  `CuspCentralBound.exists_norm_cuspFunction_le F T'`, so that
  `|φ'(g)| ≤ C' |det g|^β`. The bound is
  `C = max 0 (C₁ + (r-t)/2 - β)`, with `C₁` from `PadWhittakerGaugeBound`.
  For `Re s > C` put `σ = Re s - (r-t)/2 + β > C₁`. Pointwise, the norm of
  the integrand `W(pad g) φ'(g) |det g|^{s-(r-t)/2}` is at most
  `C' · |W(pad g)| |det g|^σ`. The integrand is left invariant under
  `N_m(F)` (`ordinaryKernel_rational_mul`), so it is measurable on the
  quotient (`out_eq_lift`, `measurable_from_quotient`). The majorant is
  measurable and left `N_m(𝔸)`-invariant. By
  `lintegral_rationalQuotient_eq` its integral over `N_m(F) \ GL_m(𝔸)`
  is the integral in `PadWhittakerGaugeBound`, which is finite.
- `ofReal_integral_norm_le_lintegral`:
  `ofReal(∫ ‖f‖ dμ) ≤ ∫⁻ ‖f‖ₑ dμ`.
- `dualWhittakerGaugeIntegrable_of_rect` (premise G'). Take `β` from
  `CuspCentralBound.exists_norm_dualCuspFunction_le F T'`, which bounds
  `|φ̃'(g)|` by `C' |det g|^β`. Take `C` and `σ` as for G, with `C₂` from
  `RectWhittakerGaugeBound`. Let `I(g) = ∫_x |W̃(rect(g, x) w')| dx` be the
  real integral in G'. It is measurable (`measurable_dualRectNormIntegral`)
  and left `N_m(𝔸)`-invariant (`dualRectNormIntegral_unipotent_mul`). The
  G' integrand `I(g) |φ̃'(g)| |det g|^{Re s-(r-t)/2}` is left
  `N_m(F)`-invariant (`dualCuspFunction_rational_mul`,
  `detPower_rational_mul`), and it is at most `C' · I(g) |det g|^σ`. The
  majorant `ofReal(I g) · ofReal(|det g|^σ)` is transferred to
  `WhittakerQuotient F m` by `lintegral_rationalQuotient_eq`. There
  `ofReal(I g)` is at most the lower integral in
  `RectWhittakerGaugeBound` (`ofReal_integral_norm_le_lintegral`), so the
  integral is finite.

`unequalGaugeReduction` combines the two lemmas. Given both statements, for
every `F, r, t, h, T, T'` it proves G from `PadWhittakerGaugeBound F h T`
and G' from `RectWhittakerGaugeBound F h T`.

Imports: `UnequalUnfoldingGaugeStatement` (the target and the premise
definitions) and the helper `CuspCentralBound`, the power bound for cusp
forms. `CuspCentralBound` has its own Markdown.
