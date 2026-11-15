# Unfolding for equal-rank cuspidal pairs

This module states the unfolding of the equal-rank global Rankin–Selberg integral
`I(s; φ, φ', Φ)` into the global Whittaker integral `Ψ(s; W, W', Φ)`, and the unfolding of
the right-hand side of its functional equation. The source is J. W. Cogdell, *Analytic
theory of L-functions for GL_n* (2004), §2.3, printed p.210 (PDF p.213) for
`I = Ψ`, and the remark after Theorem 2.2 on printed p.211 (PDF p.214) for the
functional-equation side. The source is registered as `cogdell-2004-analytic-theory-gln`.
The integrals are defined in `Langlands.Global.RankinSelberg.EqualIntegrals`. The cusp forms
`cuspFunction`, their Whittaker functions `cuspWhittaker` and the contragredient convention
`dualFunction` come from `Langlands.Global.RankinSelberg.UnequalIntegrals`. The measure
`whittakerQuotientMeasure` comes from `Langlands.Global.RankinSelberg.WhittakerIntegrals`.
All declarations are in the namespace `Langlands.Global.RankinSelbergGlobal`.

The two local instances `equalUnfoldingSchemeAffine` and `equalUnfoldingSchemeSmooth` repeat
the Library's facts that `GL_n` is affine and smooth, for the adelic points. They are
`local` and add no hypotheses.

## The statement

`EqualUnfoldingStatement` says the following. Let `F` be a number field, in an arbitrary
universe `u`, with the Library's standing hypothesis `CompactSpace (AdeleQuotient F)`. Let
`n = r + 1`, and let `T`, `T'` be actual cuspidal realizations
(`Automorphic.CuspidalOperatorRealization F r`) of `GL_n`. Let `ω`, `ω'` be continuous
characters of `F^× \ 𝔸^×` with `T.realization.HasCentralCharacter ω` and
`T'.realization.HasCentralCharacter ω'`, and put `η = ω ω'` (`ω * ω'` in Lean). Then there
is a real `C ≥ 0` with the following property. Let `ψ` be a continuous nontrivial unitary
character of `𝔸` trivial on `F` (`IsStandardAdditiveCharacter`), let `v ∈ T`, `v' ∈ T'`
and `Φ ∈ S(𝔸^n)`. Write:

* `φ`, `φ'` for the cusp forms of `v`, `v'` (`cuspFunction`);
* `W = W_φ = cuspWhittaker F T ψ v` and `W' = W'_φ' = cuspWhittaker F T' ψ⁻¹ v'`, the
  Library's global Whittaker functions `generalLinearWhittakerFunction` for the standard
  generic character of `ψ`, respectively `ψ⁻¹` (all simple-root coefficients one), with the
  measure of total mass one on `N_n(F) \ N_n(𝔸)`;
* `φ̃(g) = φ(w_n ᵗg⁻¹)`, `φ̃'(g) = φ'(w_n ᵗg⁻¹)`, `W̃(g) = W(w_n ᵗg⁻¹)` and
  `W̃'(g) = W'(w_n ᵗg⁻¹)` (`dualFunction`);
* `Φ̂ = fourierTransform F n ψ Φ`.

Then:

1. **Right half-plane.** For every `s` with `Re s > C`, the integrand of
   `I(s; φ, φ', Φ) = equalIntegral F η φ φ' Φ s` is integrable on
   `Z_n(𝔸) GL_n(F) \ GL_n(𝔸)` for `centralQuotientMeasure F n`, the integrand of
   `Ψ(s; W, W', Φ) = equalWhittakerIntegral F W W' Φ s` is integrable on
   `N_n(𝔸) \ GL_n(𝔸)` for `whittakerQuotientMeasure F n`, and
   `I(s; φ, φ', Φ) = Ψ(s; W, W', Φ)`.
2. **Left half-plane.** For every `s` with `Re s < -C`, the integrand of
   `I(1 - s; φ̃, φ̃', Φ̂) = equalIntegral F η⁻¹ φ̃ φ̃' Φ̂ (1 - s)` is integrable for
   `centralQuotientMeasure F n`, the integrand of
   `Ψ(1 - s; W̃, W̃', Φ̂) = equalWhittakerIntegral F W̃ W̃' Φ̂ (1 - s)` is integrable for
   `whittakerQuotientMeasure F n`, and `I(1 - s; φ̃, φ̃', Φ̂) = Ψ(1 - s; W̃, W̃', Φ̂)`.

The bound `C` is chosen after `T`, `T'` (and their central characters, which `T`, `T'`
determine) and before `ψ`, the vectors and `Φ`. So the half-planes depend only on the two
cuspidal realizations, as the task requires. Taking one bound `C` for both half-planes only
shrinks the source's unspecified half-planes. Every integrability claim and both identities
are in the conclusion. No binder supplies an integral, a convergence property or an
identity.

## The two sides

`equalIntegral` integrates `φ(g) φ'(g) E(g, Φ; s, η)` at the representative `q.out` of a
class of `Z_n(𝔸) GL_n(F) \ GL_n(𝔸)`. With `η = ω ω'` this integrand does not depend on the
representative; see `Langlands.Global.RankinSelberg.EqualAnalyticStatement`. Here `E` is the
series `eisensteinSeries` itself, which converges absolutely for `Re s` large
(`Langlands.Global.RankinSelberg.EisensteinStatement`).

`equalWhittakerIntegral` integrates `W(g) W'(g) Φ(e_n g) |det g|^s` at the representative
`q.out` of a class of `N_n(𝔸) \ GL_n(𝔸)`. This integrand does not depend on the
representative: `W(ug) = ψ_N(u) W(g)` and `W'(ug) = ψ_N(u)⁻¹ W'(g)` for `u ∈ N_n(𝔸)`, and
`e_n u = e_n`, `|det u| = 1`.

On the left half-plane, `W̃` is the Whittaker function of `φ̃` for `ψ⁻¹`, and `W̃'` is the one
of `φ̃'` for `ψ`. Indeed, the substitution `u ↦ w_n ᵗu⁻¹ w_n` preserves `N_n(F) \ N_n(𝔸)` and
its measure of mass one, and turns `ψ_N` into `ψ_N⁻¹`. So clause 2 is clause 1 for the pair
`φ̃`, `φ̃'`, the character `ψ⁻¹`, the central character `η⁻¹` of `φ̃ φ̃'`, the function
`Φ̂ ∈ S(𝔸^n)` and the point `1 - s`.

## The measures, and why the constant is one

The identity `I = Ψ` holds with constant one for the measures of the definition module.

* `centralQuotientMeasure F n` is the image of the quotient Haar measure on
  `GL_n(F) \ GL_n(𝔸)` restricted to `1 ≤ |det g| < e^n`. The section uses
  `d^×a = ideleMeasure F`, for which `F^× \ {1 ≤ |a| < e}` has volume one.
* Unfolding the Eisenstein series turns `I` into an integral over `P'_n(F) \ GL_n(𝔸)`, with
  `P'_n = Z_n P_n`. The integral over `a ∈ 𝔸^×` of the section and the integral over
  `Z_n(F) \ Z_n(𝔸)` combine. What remains for each `g` is the volume of
  `{a ∈ F^× \ 𝔸^× : 1 ≤ |a|^(-n) |det g| < e^n}`. This set is a translate of
  `F^× \ {e^(-1) < |a| ≤ 1}`, whose image under `a ↦ a⁻¹` is `F^× \ {1 ≤ |a| < e}`. So it
  has volume one. The result is Cogdell's
  `∫_(P_n(F) \ GL_n(𝔸)) φ(g) φ'(g) Φ(e_n g) |det g|^s dg` (p.210), for the quotient of the
  Haar measure of `GL_n(𝔸)` by counting measure on `P_n(F)`.
* The Fourier expansion `φ(g) = Σ_(γ ∈ N_n(F) \ P_n(F)) W_φ(γ g)` holds for the Library's
  Whittaker function, whose measure on `N_n(F) \ N_n(𝔸)` has mass one. Unfolding it gives an
  integral over `N_n(F) \ GL_n(𝔸)`. `whittakerQuotientMeasure F n` is the image of the
  quotient Haar measure on `N_n(F) \ GL_n(𝔸)`. So integrating over `N_n(F) \ N_n(𝔸)` first
  produces `W'_φ'` with no constant.

## Comparison with the source

Cogdell (p.210): "We have yet to check that our integrals are Eulerian. To this end we take
the integral, replace the Eisenstein series by its definition, and unfold we find
`I(s; φ, φ', Φ) = ∫_(P_n(k) \ GL_n(𝔸)) φ(g) φ'(g) Φ(e_n g) |det(g)|^s dg`. We next replace
`φ` by its Fourier expansion and unfold as before to find
`I(s; φ, φ', Φ) = Ψ(s; W_φ, W'_φ', Φ) = ∫_(N_n(𝔸) \ GL_n(𝔸)) W_φ(g) W'_φ'(g) Φ(e_n g)
|det(g)|^s dg`. This expression converges for `Re(s) ≫ 0`." After Theorem 2.2 (p.211): "We
remark in passing that the right-hand side of the functional equation also unfolds as
`I(1 - s; φ̃, φ̃', Φ̂) = ∫_(N_n(𝔸) \ GL_n(𝔸)) W̃_φ(g) W̃'_φ'(g) Φ̂(e_n g) |det(g)|^(1-s) dg`
… with convergence for `Re(s) ≪ 0`."

* **Whittaker functions.** Cogdell's `W_φ` is for `ψ` and `W'_φ'` for `ψ⁻¹` (p.206). Here
  they are the Library's `generalLinearWhittakerFunction`, as the task requires. His `W̃_φ`
  is `W_φ(w_n ᵗg⁻¹)`, as in `dualFunction`.
* **Central characters and unitarity.** Cogdell's `π`, `π'` are unitary with central
  characters `ω`, `ω'` and `η = ω ω'` (p.208). Here `ω`, `ω'` are data with the Library's
  `HasCentralCharacter` hypotheses, as the task allows, and need not be unitary. Unitarity
  plays no role in the unfolding. It only moves the half-plane of convergence, which is
  existential.
* **The Euler product.** The factorization `Ψ = ∏_v Ψ_v` for decomposable data (p.210 and
  Theorem 2.2) is not part of this statement; the partial Euler factorization is a separate
  statement.
* **Fourier transform.** `Φ̂` is taken for the self-dual (covolume-one) Haar measure on `𝔸^n`;
  see `Langlands.Global.RankinSelberg.SchwartzBruhat`. The left-half-plane identity uses
  `Φ̂` only as an element of `S(𝔸^n)`, so its normalization does not matter here.
* **Notation.** `η` is written `ω * ω'` in Lean and `χ` in the definition module, because `η`
  is a reserved token under `open scoped CategoryTheory.MonObj`.
