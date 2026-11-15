# Global analytic theory for equal-rank cuspidal pairs

This module states the analytic clauses and the functional equation of J. W. Cogdell,
*Analytic theory of L-functions for GL_n* (2004), §2.3, Theorem 2.2, printed p.211
(PDF p.214), for the global integral `I(s; φ, φ', Φ)` of two cusp forms on `GL_n`. The
source is registered as `cogdell-2004-analytic-theory-gln`. The discussion that precedes the
theorem is on printed pp.208–210 (PDF pp.211–213). The objects are defined in
`Langlands.Global.RankinSelberg.EqualIntegrals`. The Schwartz–Bruhat space
`schwartzBruhat` and the Fourier transform `fourierTransform` are defined in
`Langlands.Global.RankinSelberg.SchwartzBruhat`. The cusp forms `cuspFunction` and the
contragredient convention `dualFunction` are defined in
`Langlands.Global.RankinSelberg.UnequalIntegrals`. The predicates `HasAtMostSimplePolesIn`
and `IsStandardAdditiveCharacter` come from `Langlands.Global.RankinSelberg.EisensteinStatement`
and `Langlands.Global.RankinSelberg.UnequalAnalyticStatement`. All declarations are in the
namespace `Langlands.Global.RankinSelbergGlobal`.

The unfolding `I = Ψ` and the Euler factorization of Theorem 2.2 are separate statements.

The two local instances `equalAnalyticSchemeAffine` and `equalAnalyticSchemeSmooth` repeat
the Library's facts that `GL_n` is affine and smooth, for the adelic points. They are
`local` and add no hypotheses.

## The helper predicate

`BoundedInVerticalStripsAwayFrom f P` says: for all reals `a ≤ b` and every `δ > 0` there is
a real `C ≥ 0` with `‖f(s)‖ ≤ C` for every `s` with `a ≤ Re s ≤ b` whose distance to every
point of `P` is at least `δ`. This is Cogdell's "bounded in vertical strips away from the
poles". When `P` is empty it is equivalent to `BoundedInVerticalStrips` of the unequal-rank
statement.

## The statement

`EqualAnalyticStatement` says the following. Let `F` be a number field, in an arbitrary
universe `u`, with the Library's standing hypothesis `CompactSpace (AdeleQuotient F)`. Let
`n = r + 1`, and let `T`, `T'` be actual cuspidal realizations
(`Automorphic.CuspidalOperatorRealization F r`) of `GL_n`. Let `ω`, `ω'` be continuous
characters of `F^× \ 𝔸^×` with `T.realization.HasCentralCharacter ω` and
`T'.realization.HasCentralCharacter ω'`, the Library's central-character predicates, and
put `η = ω ω'` (`ω * ω'` in Lean). Let `ψ` be a continuous nontrivial unitary character of
`𝔸` trivial on `F` (`IsStandardAdditiveCharacter`). Let `v ∈ T`, `v' ∈ T'` and
`Φ ∈ S(𝔸^n)`. Write `φ`, `φ'` for the cusp forms of `v`, `v'` (`cuspFunction`),
`φ̃(g) = φ(w_n ᵗg⁻¹)` and `φ̃'(g) = φ'(w_n ᵗg⁻¹)` (`dualFunction`), and
`Φ̂ = fourierTransform F n ψ Φ`. Then there are a real `σ₀` and functions
`I, Ĩ : ℂ → ℂ` such that:

1. **Convergence.** For every `s` with `Re s > σ₀`:
   * the integrand `φ(g) φ'(g) E(g, Φ; s, η)` of `equalIntegral F η φ φ' Φ s` is integrable
     on `Z_n(𝔸) GL_n(F) \ GL_n(𝔸)` for `centralQuotientMeasure F n`;
   * the integrand `φ̃(g) φ̃'(g) E(g, Φ̂; s, η⁻¹)` of
     `equalIntegral F η⁻¹ φ̃ φ̃' Φ̂ s` is integrable for the same measure;
   * `I(s) = I(s; φ, φ', Φ)` and `Ĩ(s) = I(s; φ̃, φ̃', Φ̂)`, the integrals of
     `equalIntegral`.
2. **Continuation and poles.** `I` has at most simple poles in `P(η)` and `Ĩ` has at most
   simple poles in `P(η⁻¹)`, in the sense of `HasAtMostSimplePolesIn` (holomorphic off the
   set, and `(s - p) f(s)` bounded on a punctured disc at each point `p` of the set).
   `P(η) = equalPoleSet F n η` is `{-w/n, 1 - w/n}` if `η = |·|^w`, and empty otherwise.
3. **Vertical strips.** `I` is bounded in vertical strips away from `P(η)`
   (`BoundedInVerticalStripsAwayFrom`).
4. **Functional equation.** For every `s ∉ P(η)`, `I(s) = Ĩ(1 - s)`, that is,
   `I(s; φ, φ', Φ) = I(1 - s; φ̃, φ̃', Φ̂)`.

`P(η⁻¹) = 1 - P(η)`, since `η⁻¹ = |·|^(-w)` when `η = |·|^w`. So `1 - s ∉ P(η⁻¹)` in
clause 4.

`I` and `Ĩ` are existentially quantified, but they are not arbitrary. `P(η)` has at most
two points, so `ℂ \ P(η)` is open and connected. `I` agrees with the integral on the
half-plane `Re s > σ₀` and is holomorphic on `ℂ \ P(η)`, so it is the unique analytic
continuation of the integral there. The same holds for `Ĩ`. Clauses 2–4 are therefore
statements about the integrals themselves. Every convergence and integrability claim is in
the conclusion. No binder supplies an integral, a continuation, a convergence property or
an identity.

## Why the integrals are well defined

`equalIntegral` evaluates its integrand at the representative `q.out` of a class
`q ∈ Z_n(𝔸) GL_n(F) \ GL_n(𝔸)`. For `Re s > σ₀` the Eisenstein series converges
absolutely (`EisensteinStatement`). Then the integrand does not depend on the
representative:

* `φ`, `φ'` and `E(·, Φ; s, η)` are left `GL_n(F)`-invariant. The series is a sum over
  `P'_n(F) \ GL_n(F)`.
* For `z` in the center, `φ(zg) φ'(zg) = ω(z) ω'(z) φ(g) φ'(g)` by the central-character
  hypotheses. The change of variables `a ↦ a z⁻¹` in the section gives
  `E(zg, Φ; s, η) = η(z)⁻¹ E(g, Φ; s, η)`. These cancel because `η = ω ω'`.
* `φ̃(zg) = ω(z)⁻¹ φ̃(g)`, so `φ̃ φ̃'` has central character `η⁻¹`, and
  `E(zg, Φ̂; s, η⁻¹) = η(z) E(g, Φ̂; s, η⁻¹)`. `φ̃` is left `GL_n(F)`-invariant because
  `φ̃(γ g) = φ((w_n ᵗγ⁻¹ w_n⁻¹) w_n ᵗg⁻¹)`.

This is why the central characters are hypotheses and `η` is their product. Integrability
in the sense of `Integrable` includes measurability of the integrand on the quotient.

## Comparison with the source

Cogdell's Theorem 2.2 reads: "Let `φ ∈ V_π` and `φ' ∈ V_π'` cusp forms on `GL_n(𝔸)` and
let `Φ ∈ S(𝔸^n)`. Then the family of integrals `I(s; φ, φ', Φ)` define meromorphic
functions of `s`, bounded in vertical strips away from the poles. The only possible poles
are simple and occur iff `π ≃ π̃' ⊗ |det|^(iσ)` with `σ` real and are then at `s = -iσ` and
`s = 1 - iσ` with residues as above. They satisfy the functional equation
`I(s; φ, φ', Φ) = I(1 - s; φ̃, φ̃', Φ̂)`."

* **Central characters.** Cogdell writes `η = ω ω'` for the central characters of `π`, `π'`
  (p.208). Here they are data with the Library's `HasCentralCharacter` hypotheses, as the
  task allows.
* **No unitarity.** Cogdell's `π`, `π'` are unitary, so `η` is unitary and the poles are at
  `s = -iσ`, `1 - iσ` with `η = |·|^(inσ)` (p.210). Here `ω`, `ω'` are arbitrary
  continuous characters. If `η = |·|^w` with `w ∈ ℂ`, the poles of the Eisenstein series
  are at `-w/n` and `1 - w/n` (see `EisensteinStatement`), and for `w = inσ` these are
  Cogdell's points. The general case reduces to the unitary one. Write
  `|ω| = |·|^(nt)` and `|ω'| = |·|^(nt')` with `t`, `t'` real, and `τ = t + t'`. Then
  `π ⊗ |det|^(-t)` and `π' ⊗ |det|^(-t')` are cuspidal with unitary central characters,
  hence unitary, and `I(s; φ, φ', Φ)` for `π`, `π'` equals `I(s + τ; ·)` for the twisted
  pair. The convergence region is therefore stated as some right half-plane
  `Re s > σ₀`.
* **Poles: "at most", not "iff".** The statement says that `I` has at most simple poles,
  located in `P(η)`. Cogdell's further assertions are omitted: that the poles occur iff
  `π ≃ π̃' ⊗ |det|^(iσ)`, and the residue formulas on p.210. The task's statement A asks
  only for meromorphic continuation with at most simple poles at these points.
* **Which function is continued.** Cogdell defines `I(s; φ, φ', Φ)` for all `s` off the
  poles by integrating against the continued Eisenstein series. Here `I` is the analytic
  continuation of the absolutely convergent integral on `Re s > σ₀`. The two agree by
  uniqueness of analytic continuation on the connected set `ℂ \ P(η)`, because the integral
  against the continued series is holomorphic there (the cusp forms are rapidly
  decreasing).
* **The dual side.** Cogdell writes the right-hand side of the functional equation with
  `φ̃(g) = φ(w_n g^ι)` and the same `φ̃'`, with the Eisenstein series for `η⁻¹`, the
  central character of `π̃ ⊗ π̃'` (p.210). `Ĩ` is exactly this integral, continued in the
  same way. The statement also asserts its convergence for `Re s > σ₀`, which makes the
  right-hand side of the functional equation meaningful; it is not an input.
* **Vertical strips.** Only `I` is asserted to be bounded in vertical strips away from
  `P(η)`. The same property of `Ĩ` follows from the functional equation, since
  `s ↦ 1 - s` maps vertical strips to vertical strips and `P(η)` to `P(η⁻¹)`.
* **Measures.** The integrals use `centralQuotientMeasure F n`, the measure `dg / d^×a` on
  `Z_n(𝔸) GL_n(F) \ GL_n(𝔸)` described in `EqualIntegrals`. Both sides of the functional
  equation use the same measure, and it is invariant under `g ↦ w_n ᵗg⁻¹`, which is what
  the functional equation needs. A different normalization would multiply `I` and `Ĩ` by the
  same constant and change nothing in the statement.
* **The Fourier transform.** `Φ̂` is taken for the self-dual (covolume-one) Haar measure on
  `𝔸^n`; see `SchwartzBruhat`. The functional equation then holds without a constant, for
  every `ψ` of the stated kind.
* **Notation.** `η` is written `ω * ω'` in Lean and `χ` in the definition modules, because
  `η` is a reserved token under `open scoped CategoryTheory.MonObj`.
