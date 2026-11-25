# Injectivity of maps from standard modules onto generic `(𝔤𝔩_n(ℝ), O(n))`-modules

## Statement proved

`Langlands.Archimedean.realGenericLanglandsQuotientInjective` proves
`Langlands.Archimedean.RealGenericLanglandsQuotientInjectiveStatement.{uV}`, stated in
`Langlands/Representation/Archimedean/RealGenericParameterReduction.lean`:

Let `(ρ, π)` be a `(𝔤𝔩_n(ℝ), O(n))`-module (`IsRealGKModule n ρ π`) that is irreducible
(`IsIrreducibleGKModule ρ π`), admissible (`IsAdmissibleGKModule ρ`) and generic
(`IsRealGenericGKModule n π`). Let `ds` be a list of real blocks with `realRank ds = n` in
Langlands order (`IsRealLanglandsOrdered ds`), and let
`B : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] V` be a nonzero
intertwiner (`IsRealStandardIntertwiner n ρ π ds B`). Then `B` is injective.

The theorem has no hypotheses beyond those of the statement, for every universe `uV` of the
module `V`.

## Proof

The proof is the single term

```lean
realGenericLargeReduction InfinitesimalCharacter.realGKModuleInfinitesimalCharacter
  Kostant.realWhittakerMaximallyFaithful realLargeLanglandsQuotientInjective
```

It applies the published reduction
`Langlands.Archimedean.realGenericLargeReduction : RealGenericLargeReductionStatement.{uV}`
(module `Langlands.Representation.Archimedean.RealGenericLargeReduction`) to three Library
theorems, one for each hypothesis of the reduction:

1. `Langlands.Archimedean.InfinitesimalCharacter.realGKModuleInfinitesimalCharacter :
   RealGKModuleInfinitesimalCharacterStatement.{uV}`
   (module `Langlands.Representation.Archimedean.RealGKInfinitesimalCharacter`): every
   irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module has an infinitesimal character, that is,
   the centre of the universal enveloping algebra of `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)` acts on `V` by scalars
   (`HasInfinitesimalCharacter π`).
2. `Langlands.Archimedean.Kostant.realWhittakerMaximallyFaithful :
   RealWhittakerMaximallyFaithfulStatement.{uV}`
   (module `Langlands.Representation.Archimedean.RealWhittakerMaximallyFaithfulProof`):
   Kostant's theorem (1978, Theorem 3.9). A `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`-module with an infinitesimal
   character and a nondegenerate algebraic Whittaker functional (`IsRealGenericGKModule n π`)
   is maximally faithful (`IsMaximallyFaithful π`).
3. `Langlands.Archimedean.realLargeLanglandsQuotientInjective :
   RealLargeLanglandsQuotientInjectiveStatement.{uV}`
   (module `Langlands.Representation.Archimedean.RealLargeLanglandsQuotientInjectiveProof`):
   Vogan's theorem (1978, Theorem 6.2, the step (a) ⇒ (f)) for `GL_n(ℝ)` and the Library's
   standard modules. If `(ρ, π)` is irreducible, admissible and maximally faithful, every nonzero
   intertwiner from a Langlands-ordered standard module of total rank `n` into it is
   injective.

Inside `realGenericLargeReduction`, item 1 gives an infinitesimal character for `π`. Item 2
and the genericity hypothesis then make `π` maximally faithful. Item 3 applied to the
hypotheses of the statement gives the injectivity of `B`.

## Scope

This file adds no new mathematics. It combines published Library theorems that prove each
hypothesis of the published reduction. The axioms used are `propext`, `Classical.choice` and
`Quot.sound`.

The source route to this result has three prerequisites. The provenance notes in
`RealGenericParameterReduction.md` and `RealGenericLargeReduction.md` describe that route. The
proof here proves the exact target without passing through two of them. These two are outside
both the result and its argument:

- **Algebraic to continuous genericity.** The proof does not show that the nonzero algebraic
  Whittaker functional of `IsRealGenericGKModule n π` gives a continuous Whittaker functional,
  that is, genericity of a representation in the topological sense. This is neither proved nor
  used. The algebraic functional enters only through item 2. That item is the algebraic
  implication in Kostant 1978, Theorem 3.9 (Matumoto 1987, Theorem 1): an infinitesimal
  character and a nondegenerate algebraic Whittaker functional make the Lie action maximally
  faithful. No continuity or topology on `V` is involved.
- **Comparison with classical standard modules.** The proof does not identify the Library's
  `realStandardModule n ds`, or its `O(n)`-finite part, with an independently defined classical
  standard module and its Harish-Chandra module. This is neither proved nor used. Item 3, the
  large-quotient theorem, is proved directly on the Library's normalized-induction function space
  `kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)`. That space carries the
  actual right-translation action `realStandardRep n ds` and the derivative action
  `realStandardLie n ds`. `StandardModule.md` gives the comparison with classical induction only
  as informal explanation. No comparison theorem is used.

The proof does pass through the remaining prerequisite, Vogan's irreducibility theorem,
in the form of item 3. That form is the Library's model with "large" read as maximally faithful
(Vogan 1978, Definition 6.1 and Theorem 6.2, step (a) ⇒ (f)). In addition, the proof neither
proves nor uses existence or uniqueness of Langlands data for an arbitrary target module (see
`RealLargeLanglandsQuotientInjectiveProof.md`).

So this theorem gives injectivity of `B` for the Library's standard modules and algebraic
genericity only. It should not be cited for continuous genericity of `π`. Nor should it be cited
for the irreducibility of a classical standard module whose Langlands quotient has a continuous
Whittaker functional (Casselman–Shahidi 1998, p. 562), or for any comparison between the
Library's model and classical induction.
