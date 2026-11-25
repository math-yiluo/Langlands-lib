# Totally complex forms of the semi-local functional equations

Module `Langlands.Global.RankinSelberg.SemilocalEquationTCStatements`.
Part of the supporting work for the partial Rankin–Selberg functional equation of cuspidal
pairs with integral gamma factors at the exceptional places
(`CuspidalPairPartialGammaEquationStatement`). It belongs to the restriction of the global
statements on the route to the local correspondence to totally complex base fields.

**Scope.** The module defines two propositions in the namespace
`Langlands.Global.RankinSelbergGlobal` and proves nothing. Each is a Library proposition
with one more instance argument, `[NumberField.IsTotallyComplex F]`, inserted directly after
`[NumberField F]`. The universe parameters are the same, and the rest of the body is copied
verbatim.

| New proposition | Universes | Original proposition | Original module |
|---|---|---|---|
| `UnequalSemilocalEquationTCStatement` | `u uQ` | `UnequalSemilocalEquationStatement` | `Langlands.Global.RankinSelberg.UnequalSemilocalEquationStatement` |
| `EqualSemilocalEquationTCStatement` | `u uQ` | `EqualSemilocalEquationStatement` | `Langlands.Global.RankinSelberg.EqualSemilocalEquationStatement` |

The two local instances of the module, `semilocalTCSchemeAffine` and
`semilocalTCSchemeSmooth`, are copies of the local instances `unequalSemilocalSchemeAffine`
and `unequalSemilocalSchemeSmooth` of the original modules (renamed because local instances
are still global declarations). They supply the same `IsAffine` and `Smooth` instances for
`Scheme F n`, which the vocabulary of the bodies needs.

## 1. The statements

All vocabulary is that of the originals, and nothing is redefined. The meaning of every
clause is explained in [`UnequalSemilocalEquationStatement`](UnequalSemilocalEquationStatement.md)
and [`EqualSemilocalEquationStatement`](EqualSemilocalEquationStatement.md). In words:

- `UnequalSemilocalEquationTCStatement.{u, uQ}`. Let `F : Type u` be a totally complex number
  field with `[CompactSpace (AdeleQuotient F)]`. Let `ψ` be a unitary character of `𝔸` trivial
  on `F`, let `T`, `T'` be actual cuspidal realizations of `GL_(r+1)`, `GL_(t+1)` with
  `t < r` and contragredient realizations `Td`, `Td'`, and let `P`, `P'` be spectral
  presentations with irreducible admissible components. Let `S` be a finite set of finite
  places that contains both exceptional sets and supports `ψ`, and fix archimedean additive
  components and parameters. Then there are vectors `x`, `x'`, spherical outside `S`, a real
  `σ` and meromorphic functions `A`, `B` on `ℂ` with the following properties. `A` and `B`
  are nonzero off a discrete set, and on `σ < Re s` they agree with the partial integrals
  `Ψ_(S∪∞)(s; W, W')` and `Ψ̃_(S∪∞)(s; ρ(w_(n,m)) W̃, W̃')`. For all components `ψ_v`,
  self-dual measures `ν_v` and integral gamma factors `G_v` of the actual local components at
  `v ∈ S`, off a discrete set,
  `L_∞(s) B(1 - s) = (∏_(v ∈ S) G_v(q_v^(-s))) ε_∞(s) L∨_∞(1 - s) A(s)`.
- `EqualSemilocalEquationTCStatement.{u, uQ}`. The same for `t = r` over a totally complex
  number field. The partial integrals are `Ψ_(S∪∞)(s; W, W', Φ)` and
  `Ψ_(S∪∞)(s; W̃, W̃', Φ̂)`, with a Schwartz–Bruhat function `Φ` that is standard outside `S`.
  `Φ` is also produced by the statement.

## 2. Effect of the restriction

Mathlib's `NumberField.IsTotallyComplex F` says that every infinite place of `F` is complex
(`Mathlib/NumberTheory/NumberField/InfinitePlace/TotallyRealComplex.lean`). So the subtype
`{v : InfinitePlace F // v.IsReal}` is empty, and:

- the quantifiers over real-place additive components `aR` and real-place parameters `dR`,
  `dR'`, `dRd`, `dRd'` range over functions on an empty type, and their hypotheses hold
  vacuously;
- in `infiniteL`, `dualInfiniteL` and `infiniteEpsilon` the products over real places are
  empty products, equal to `1`.

So the totally complex forms involve the archimedean local theory only at complex places
(`GL_n(ℂ) × GL_m(ℂ)`: the factors `complexPairLFactor` and `complexPairEpsilon`). The bodies
keep the real-place clauses verbatim, so that each new proposition differs from its original
only by the instance argument.

## 3. Relation to the originals

Each original implies its totally complex form at the same universe levels: apply the
original to the same field and forget the new instance (`fun h F _ _ _ _ => h F`). The
converse is not claimed. The statements make no claim about number fields with a real place.
Totally complex number fields exist (for example `ℚ(i)`, or any CM field; Mathlib
`NumberField.IsCMField.isTotallyComplex`), so the statements are not vacuous.

## 4. Use

The two propositions are used, in a separate module (`CuspidalPairPartialGammaGlobalTCReduction`), as premises of a totally complex
form of `CuspidalPairPartialGammaGlobalReductionStatement`
([`CuspidalPairPartialGammaGlobalReduction`](../Factors/CuspidalPairPartialGammaGlobalReduction.md)),
whose conclusion is `Langlands.Global.CuspidalPairPartialGammaEquationTCStatement`. That
reduction takes them in place of the two unrestricted semi-local equations, which are the
only premises of `CuspidalPairPartialGammaGlobalReductionStatement` that involve real
places.

## 5. Sources and provenance

Provenance: *derived*. The two propositions are the special cases, for totally complex base
fields, of the Library statements. Those statements follow the source below, which states
its results for every number field. The locators are those of the originals; the full
correspondence, including the normalizations, is in the Markdown of the originals.

- `cogdell-2004-analytic-theory-gln` (Cogdell 2004; PDF page = printed page + 3): proof of
  Theorem 4.1, printed pp.219–220; Theorem 3.2 (nonarchimedean local functional equation),
  printed p.214; §3.2, printed pp.216–217 (archimedean local theory).
