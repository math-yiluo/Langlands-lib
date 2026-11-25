# The central sign over the infinite places and `S`

Module `Langlands.Global.RankinSelberg.ArchimedeanCentralSignStatement`, namespace
`Langlands.Global.RankinSelbergGlobal`. It states the central-sign relation behind the
semi-local functional equations, the cancellation of
the central signs in Cogdell 2004, proof of Theorem 4.1, p.220.

## Statement

`ArchimedeanCentralSignStatement` is `Prop`-valued, with the universes `u` (number field) and
`uQ` (presentation) free. For

* a number field `F` with `AdeleQuotient F` compact,
* any `t` and an actual cuspidal realization `T'` of `GL_(t+1)`,
* a spectral presentation `P'` of `T'` with irreducible admissible components
  (`HasIrreducibleAdmissibleComponents P'`),
* a finite set `S` of finite places with `P'.exceptional ⊆ S`,
* any family `ψv` of nontrivial additive characters of the completions `F_v` at the finite
  places (`Correspondence.NontrivialAdditiveCharacter (padicField v)`),
* and `ζ : S → ℂ^×` such that for each `v ∈ S` there is a nonzero Whittaker functional
  `ℓ ∈ glInverseFunctionals (ψv v) t σ_v` with `HasModelMinusOneScalar σ_v ℓ (ζ v)`, where
  `σ_v = ((P'.localComponent v).padicObject …).obj.representation` is the actual local
  component of `P'` at `v` (with the canonical topology of `F_v`),

it asserts

`(∏_(v real) ω'_v(−1)) · (∏_(w complex) ω'_w(−1)) · ∏_(v ∈ S) ζ_v = 1`,

with `ω'_v(−1) = realMinusOneScalar T' v` and `ω'_w(−1) = complexMinusOneScalar T' w`, the
defined scalars of `−1` at the infinite places (module `ArchimedeanPlaces`), the same scalars
as in the sign of result 1.

`HasModelMinusOneScalar σ ℓ ζ` says that every function `f` of the coefficient model of `ℓ`
satisfies `f((−1) g) = ζ f(g)`. For `ℓ ≠ 0` such a `ζ` is unique
(`HasModelMinusOneScalar.unique`), and it is `ω_(σ_v)(−1)`.

## Why it holds

Let `ω'` be the central character of the cuspidal representation of `T'`, a character of
`𝔸^× / F^×`. The element `−1 ∈ F^×` is rational, so `ω'(−1) = ∏_v ω'_v(−1) = 1` over all places.

* At an infinite place `v`, `−1 ∈ O(t+1)` or `U(t+1)` acts on `T'` at `v` by `ω'_v(−1)`; this
  is the defined scalar.
* At `v ∈ S`, `σ_v` is irreducible admissible, so `−1` acts on it by the scalar `ω'_v(−1)`
  (Schur's lemma). For `f = ℓ(σ_v(·) y)` in the model, `f((−1) g) = ℓ(σ_v(−1) σ_v(g) y) =
  ω'_v(−1) f(g)`, so `ζ_v = ω'_v(−1)` by uniqueness.
* At a finite `v ∉ S`, `v ∉ P'.exceptional`. The tensor-exceptional set of the presentation
  is contained in `P'.exceptional`, so the reference vector at `v` is a nonzero vector fixed
  by `GL_(t+1)(𝒪_v)`, and the local class is spherical
  (`Langlands.Automorphic.FiniteTensorPresentation.UnramifiedData.isSphericalClass`). The
  element `−1` lies in `GL_(t+1)(𝒪_v)` and fixes this vector, so `ω'_v(−1) = 1`.

The product over all places therefore reduces to the left side of the statement.

The scalar `ζ_v` does not depend on `ψv v`, so the statement holds for any family `ψv`. The
consumers apply it to the canonical components of `ψ`, with the functional `ℓ` of their test
data: `PadicUnequalTestData.inverseFunctional` (unequal ranks) or `EqualLocalTestData.ℓ'`
(equal ranks), whose `HasMinusOneScalar` is by definition `HasModelMinusOneScalar` for that
functional.

## Use in the targets

Raised to the power `r`, the statement gives
`(∏_(v ∈ S) ζ_v^r) · ∏_(v | ∞) ω'_v(−1)^r = 1`. The sign of result 1 multiplied over the infinite
places is `∏_(v | ∞) ω'_v(−1)^r`, so in the unequal-rank target it cancels against
`∏_(v ∈ S) ζ_v^r`, and in the equal-rank target it is the constant `κ`, with
`κ ∏_(v ∈ S) ζ_v^r = 1`. See the Markdown of `ArchimedeanSemilocalTheoryStatement`.

## Comparison with the source

Cogdell (p.220) writes the cancellation as `∏_(v ∈ S ∪ ∞) ω'_v(−1)^(n−1) = ω'(−1)^(n−1) = 1`, with
`S` containing the archimedean places. Here `S` is a set of finite places, the infinite
places are listed separately, and the statement is made without the exponent; the exponent
`n − 1 = r` is applied by the consumers.

## Choices of form

* **Universal `ζ`.** `ζ_v` is any scalar with the property for some nonzero functional; by
  uniqueness this is no stronger than asserting it for one.
* **Any `ψv`.** No condition is put on `ψv`, which only strengthens the statement.
* The module declares the same two local instances as the targets (affineness and smoothness
  of the group scheme `GL_n`).

## Sources

* J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004),
  `cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3), proof of Theorem 4.1,
  p.220.

## Provenance

Source statement: Cogdell 2004, p.220, the product formula for `ω'(−1)`, restricted to the
places where the local factor can be nontrivial.
