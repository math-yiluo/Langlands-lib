# Totally complex forms of the cuspidal-pair functional equation and its parts

Author: Worker 0. Statement contribution to Task 0
(`69dd20b3-6a77-44aa-b779-32391843c8dd`), revision 1, as decided in the
operator's answer `81ed24709e7050068786116ca6613260` (Option A) to request
`9b5f630f11af591aae45e2157df43d94`.

**Scope.** The module
`Langlands.Global.Factors.CuspidalPairFunctionalEquationTCStatement` defines three
propositions in the namespace `Langlands.Global` and proves nothing. Each is a
published proposition with one more instance argument,
`[NumberField.IsTotallyComplex F]`, inserted directly after `[NumberField F]`. The
universe parameters are the same, and the rest of the body is copied verbatim.

| New proposition | Universes | Published original | Original module |
|---|---|---|---|
| `CuspidalArchimedeanParameterExistenceTCStatement` | `u` | `CuspidalArchimedeanParameterExistenceStatement` | `Langlands.Global.Factors.CuspidalPairFunctionalEquationReduction` |
| `CuspidalPairCompletedEquationTCStatement` | `u uQ` | `CuspidalPairCompletedEquationStatement` | `Langlands.Global.Factors.CuspidalPairFunctionalEquationReduction` |
| `CuspidalPairGlobalFunctionalEquationTCStatement` | `u uQ` | `CuspidalPairGlobalFunctionalEquationStatement` | `Langlands.Global.Factors.CuspidalPairFunctionalEquationStatement` |

The principal declaration of the unit is
`Langlands.Global.CuspidalPairGlobalFunctionalEquationTCStatement`.

## 1. The statements

All vocabulary is that of the originals, and nothing is redefined. The finite places
use `FinitePairFactorChoice`, `IsUnramifiedOutside` and `CompletedEquationHolds`
(`CuspidalPairFactorData`). The infinite places use
`OperatorRealization.HasRealPlaceParameter` and `HasComplexPlaceParameter`, the
additive components `IsRealAdditiveComponent` and `IsComplexAdditiveComponent`, and
the archimedean pair factors `realPairLFactor`, `realPairEpsilon`,
`complexPairLFactor` and `complexPairEpsilon`. The meaning of every clause is
explained in `CuspidalPairFunctionalEquationStatement.md` §§2–5 and in
`CuspidalPairFunctionalEquationReduction.md` §1. In words:

- `CuspidalArchimedeanParameterExistenceTCStatement.{u}`. For every totally complex
  number field `F : Type u` with `[CompactSpace (AdeleQuotient F)]`, every `r : ℕ`
  and every actual cuspidal realization `T` of `GL_(r+1)` over `F`
  (`Automorphic.CuspidalOperatorRealization F r`), the realization has a real-place
  parameter `ds` at every real place and a complex-place parameter at every complex
  place.
- `CuspidalPairCompletedEquationTCStatement.{u, uQ}`. For every totally complex
  number field `F` with the compactness instance, every nontrivial unitary additive
  character `ψ` of the adeles trivial on `F`, every pair of cuspidal realizations
  with their contragredients and spectral presentations (in universes `u`, `uQ`) with
  irreducible admissible components, every finite set `S` of finite places that
  contains the four exceptional sets and supports `ψ`, every finite factor choice `c`
  unramified outside `S`, and every choice of archimedean additive components and
  archimedean parameters, the completed equation `c.CompletedEquationHolds S L∞ L∞∨
  ε∞` holds for the archimedean factors built from these parameters.
- `CuspidalPairGlobalFunctionalEquationTCStatement.{u, uQ}`. For the same data over a
  totally complex number field, the local data exist (a finite factor choice, and at
  every infinite place an additive component of `ψ` and parameters of the four
  realizations), and there is one finite set `S` such that every finite factor
  choice is unramified outside `S` and satisfies the completed equation for every
  choice of archimedean data.

## 2. Effect of the restriction

Mathlib's `NumberField.IsTotallyComplex F` says that every infinite place of `F` is
complex (`Mathlib/NumberTheory/NumberField/InfinitePlace/TotallyRealComplex.lean`).
So the subtype `{v : InfinitePlace F // v.IsReal}` is empty, and:

- the real-place clause of `CuspidalArchimedeanParameterExistenceTCStatement` and the
  real-place clause of the existence part of
  `CuspidalPairGlobalFunctionalEquationTCStatement` hold vacuously;
- in both completed equations, the quantifiers over real-place additive components
  `aR` and real-place parameters `dR`, `dR'`, `dRd`, `dRd'` range over functions on an
  empty type, and the products over real places in `L∞`, `L∞∨` and `ε∞` are empty
  products, equal to `1`.

The bodies keep these clauses verbatim, as the operator's answer requires, so that
each new proposition differs from its original only by the instance argument. The
complex places remain. A proof of the first statement still needs the
`GL_n(ℂ)` parameters, whose nonvanishing input is open in Task 7065.

## 3. Relation to the originals

Each original implies its totally complex form at the same universe levels: apply
the original to the same field and forget the new instance. A private development
check of Worker 0 compiled the three implications, each as
`fun h F _ _ _ _ => h F`. The converse is not claimed. The statements make no claim
about number fields with a real place.

The totally complex form of the published reduction
`CuspidalPairFunctionalEquationReductionStatement` (the local data, the parameters
and the completed equation imply the functional equation) is stated separately, in
`Langlands.Automorphic.AssociatedFactorTCReductionStatement`, as
`Langlands.Global.CuspidalPairFunctionalEquationReductionTCStatement`. Its first
input, `CuspidalPairLocalDataStatement`, has no archimedean clause and is not
restricted.

## 4. Why the totally complex forms are stated

The goal of Task 0 is local. In the Library's route to the local correspondence
(route note `notes/henniart/llc-proof-route.md`), these statements are needed only
over the number fields produced by the globalization of Henniart (2000) §3 and
Harris (1998) §4: a CM base field and its finite extensions (Galois closures,
Brauer-induction fields, cyclic towers). A CM field is totally complex (Mathlib
`NumberField.IsCMField.isTotallyComplex`), and every finite extension of a totally
complex field is totally complex (`NumberField.isTotallyComplex_of_algebra`).
Restricting the global inputs to totally complex fields therefore loses nothing on
the route. It removes the real-place (`GL_n(ℝ)`) archimedean theory from the
critical path. The unrestricted statements stay the targets of their tasks
(Tasks 5720 and 5493) as infrastructure. The operator asked their owners to stage
the totally complex forms as supporting proof candidates.

## 5. Sources and provenance

Provenance: *derived*. The three propositions are the special cases, for totally
complex base fields, of the published statements. Those statements follow the
sources below, which state their results for every number field. The sources and
locators are those of the originals; the full correspondence, including the
normalizations and the source-to-application gaps, is in
`CuspidalPairFunctionalEquationStatement.md` §§1 and 3–6.

- `cogdell-2004-analytic-theory-gln` (Cog04): Theorem 4.1, printed p.219 (PDF 222),
  the global functional equation of `L(s, π × π')` for cuspidal `π`, `π'`, with the
  archimedean factors of §3.2, p.216 (PDF 219).
- `getz-hahn-2024-automorphic-representations` (GH): Theorem 11.7.1, printed p.309
  (PDF 320), for the completed function `Λ(s, π × π')` of (11.23)–(11.24), p.308
  (PDF 319).
- `knapp-1994-archimedean-llc` (Knapp): Theorem 4, printed p.405 (PDF 415), the
  classification of the irreducible admissible representations of `GL_n(ℂ)`, and
  Theorem 5, printed p.406 (PDF 416), the local Langlands correspondence for
  `GL_n(ℂ)`; these lie behind the complex-place parameters. (Knapp's Theorems 1–2,
  pp.400–403, treat `GL_n(ℝ)`; after the restriction to totally complex fields the
  real-place clauses are vacuous, so they are not needed here.)
- `jacquet-2009-archimedean-rankin-selberg` (Jac09): Theorem 2.1, p.6, the
  archimedean pair integrals and the Weil-side factors.
- `henniart-2000-simple-proof` (H00): §2.3, printed pp.444–445 (PDF 6–7), where the
  global functional equations are used for Théorème 2.3.
