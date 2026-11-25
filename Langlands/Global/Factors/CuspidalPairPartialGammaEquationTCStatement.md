# Totally complex form of the partial equation of cuspidal pairs with integral gammas

Module `Langlands.Global.Factors.CuspidalPairPartialGammaEquationTCStatement`. It belongs to
the restriction of the global statements on the route to the local correspondence to totally
complex base fields (`CuspidalPairFunctionalEquationTCStatement.md` §4).

**Scope.** The module defines one proposition and proves nothing:
`Langlands.Global.CuspidalPairPartialGammaEquationTCStatement.{u, uQ}`. It is the published
`Langlands.Global.CuspidalPairPartialGammaEquationStatement.{u, uQ}` (module
`Langlands.Global.Factors.CuspidalPairPartialGammaReduction`, called (G') there) with one more
instance argument, `[NumberField.IsTotallyComplex F]`, inserted directly after
`[NumberField F]`. The universe parameters are the same, and the rest of the body is copied
verbatim.

## 1. The statement

All vocabulary is that of (G'), and nothing is redefined; the meaning of every clause is
explained in [`CuspidalPairPartialGammaReduction`](CuspidalPairPartialGammaReduction.md). In
words: let `F : Type u` be a totally complex number field with
`[CompactSpace (AdeleQuotient F)]` and `ψ` a nontrivial unitary character of `𝔸` trivial on
`F`. Take cuspidal realizations `T`, `T'` of `GL_(r+1)`, `GL_(t+1)` with contragredients
`Td`, `Td'`, and spectral presentations `P`, `P'`, `Pd`, `Pd'` (in universes `u`, `uQ`) with
irreducible admissible components. Let `S` be a finite set of finite places containing the
four exceptional sets and supporting `ψ`, and fix archimedean additive components and
parameters. Then there are a real `σ` and functions `Λ`, `Λd`, meromorphic on `ℂ`, such that:

* for `Re s > σ`, whenever the Euler product `∏_(v ∉ S) L(s, Π_v × Π'_v)` of the unramified
  factors converges to `p`, `Λ(s) = L_∞(s) p`; likewise `Λd(s) = L∨_∞(s) pd` for the
  contragredient pair;
* for every family of components `ψ_v` of `ψ`, self-dual measures `ν_v` and integral gamma
  factors `G_v` of the actual local components at the places `v ∈ S`, off a discrete set
  `Λ(s) = (∏_(v ∈ S) G_v(q_v^(-s))) ε_∞(s) Λd(1 - s)`.

## 2. Effect of the restriction

Mathlib's `NumberField.IsTotallyComplex F` says that every infinite place of `F` is complex
(`Mathlib/NumberTheory/NumberField/InfinitePlace/TotallyRealComplex.lean`). So the subtype
`{v : InfinitePlace F // v.IsReal}` is empty. The quantifiers over the real-place data `aR`,
`dR`, `dR'`, `dRd`, `dRd'` range over functions on an empty type, their hypotheses hold
vacuously, and the products over real places in `L_∞`, `L∨_∞` and `ε_∞` are empty products,
equal to `1`. The archimedean factors that remain are those of the complex places
(`complexPairLFactor`, `complexPairEpsilon`).

## 3. Relation to the original

(G') implies its totally complex form at the same universe levels: apply it to the same field
and forget the new instance (`fun h F _ _ _ _ => h F`). The converse is not claimed. Totally
complex number fields exist (for example `ℚ(i)`, or any CM field; Mathlib
`NumberField.IsCMField.isTotallyComplex`), so the statement is not vacuous.

## 4. Use

It is defined once here so that the totally complex completed equation
(`CuspidalPairPartialGammaTCReduction`) and the totally complex global reduction
(`CuspidalPairPartialGammaGlobalTCReduction`) import the same proposition. The latter derives
it from the global Rankin–Selberg statements with totally complex semi-local equations
(`Langlands.Global.RankinSelbergGlobal.UnequalSemilocalEquationTCStatement`
and `EqualSemilocalEquationTCStatement`, module
`Langlands.Global.RankinSelberg.SemilocalEquationTCStatements`).

## 5. Sources and provenance

Provenance: *derived*. The proposition is the special case, for totally complex base fields,
of the published (G'). (G') follows the source below, which states its result for every number
field.

- `cogdell-2004-analytic-theory-gln` (Cogdell 2004; PDF page = printed page + 3): proof of
  Theorem 4.1, printed pp.219–220.
