# Archimedean standard-module parameters of actual cuspidal realizations

Authors: Worker 20, with Worker 174 (the global generic-component results used below). Worker
673 (Task 7041) supplied the composition of the `GL_n(ℝ)` input from the published real
reductions and their proved inputs. This is the proof of the target of Task 5720
(`a2cfc970-9e20-4d56-b053-8f91a2e0b5cc`).

## Statement proved

`Langlands.Global.cuspidalArchimedeanParameterExistence :
CuspidalArchimedeanParameterExistenceStatement.{u}` proves the Library statement
`Langlands.Global.CuspidalArchimedeanParameterExistenceStatement` (module
`Langlands.Global.Factors.CuspidalPairFunctionalEquationReduction`). It keeps the universe `u`
and adds no hypotheses. The statement is:

for every number field `F : Type u` with `[CompactSpace (AdeleQuotient F)]`, every `r : ℕ` and
every actual cuspidal realization `T : Automorphic.CuspidalOperatorRealization F r` of
`GL_(r+1)`,

1. at every real place `v` of `F` there is a list `ds` of real blocks with
   `OperatorRealization.HasRealPlaceParameter T.realization v ds`; and
2. at every complex place `v` of `F` there is a list `ds` of complex characters with
   `OperatorRealization.HasComplexPlaceParameter T.realization v ds`.

`HasRealPlaceParameter` (module `Langlands.Automorphic.ArchimedeanPlaceParameter`) asks that
the blocks `ds` have total rank `r + 1`, and that some injective linear map sends the
`O(r+1)`-finite functions of the standard module of `ds` into the space of `T.realization`.
This map must carry right translation to the compact action at `v`, and right derivatives to
the Lie action at `v`. `HasComplexPlaceParameter` is the same with `U(r+1)`, the complex
principal series of `ds`, and length `r + 1`.

## Proof

The Lean proof is a single term. It applies the published reduction
`Langlands.Automorphic.cuspidalArchimedeanParameterReduction` (module
`Langlands.Automorphic.ArchimedeanParameterReduction`), which proves
`RealGenericStandardParameterStatement → ComplexGenericStandardParameterStatement →
CuspidalArchimedeanGenericComponentStatement → CuspidalArchimedeanParameterExistenceStatement`.
The proof gives it three proved premises.

**1. The `GL_n(ℝ)` input `RealGenericStandardParameterStatement`.** Every irreducible
admissible generic `(𝔤𝔩_n(ℝ), O(n))`-module has the standard-module parameter of some list of
real blocks. No single Library theorem proves this statement yet (Task 5975 is its own task).
The proof builds it inline from three published reductions and five proved theorems, all in
`Langlands.Representation.Archimedean`:

- `Archimedean.realGenericStandardParameterReduction` (module `RealGenericParameterReduction`)
  proves `RealLanglandsQuotientStatement → RealGenericLanglandsQuotientInjectiveStatement →
  RealGenericStandardParameterStatement`.
- Its first premise comes from `Archimedean.realLanglandsQuotientReduction` (module
  `RealLanglandsQuotientReduction`), which proves `RealPrincipalSeriesQuotientStatement →
  RealLanglandsFromPrincipalSeriesStatement → RealLanglandsQuotientStatement`. The proof
  applies it to
  - `Archimedean.realPrincipalSeriesQuotient` (module `RealPrincipalSeriesQuotientProof`):
    Casselman's theorem in quotient form, every irreducible admissible module receives a
    nonzero standard intertwiner from the `O(n)`-finite principal series of `n` real
    characters; and
  - `Archimedean.realLanglandsFromPrincipalSeries` (module
    `RealLanglandsFromPrincipalSeriesProof`): the Langlands classification starting from a
    principal-series quotient gives a nonzero intertwiner from a standard module in Langlands
    order.
- Its second premise comes from `Archimedean.realGenericLargeReduction` (module
  `RealGenericLargeReduction`), which proves `RealGKModuleInfinitesimalCharacterStatement →
  RealWhittakerMaximallyFaithfulStatement → RealLargeLanglandsQuotientInjectiveStatement →
  RealGenericLanglandsQuotientInjectiveStatement`. The proof applies it to
  - `Archimedean.InfinitesimalCharacter.realGKModuleInfinitesimalCharacter` (module
    `RealGKInfinitesimalCharacter`): irreducible admissible modules have an infinitesimal
    character;
  - `Archimedean.Kostant.realWhittakerMaximallyFaithful` (module
    `RealWhittakerMaximallyFaithfulProof`): Kostant's theorem, a generic module with an
    infinitesimal character is maximally faithful (large); and
  - `Archimedean.realLargeLanglandsQuotientInjective` (module
    `RealLargeLanglandsQuotientInjectiveProof`): Vogan's theorem, a nonzero standard
    intertwiner from a standard module in Langlands order of rank `n` into a maximally
    faithful (large) irreducible admissible module is injective.

So the nonzero intertwiner given by the Langlands classification is injective, which is a
standard-module parameter.

**2. The `GL_n(ℂ)` input.** `Archimedean.complexGenericStandardParameter :
ComplexGenericStandardParameterStatement` (module
`Langlands.Representation.Archimedean.ComplexGenericStandardParameterProof`) gives every
irreducible admissible generic `(𝔤𝔩_n(ℂ), U(n))`-module a standard-module parameter.

**3. The global generic-component statement.**
`Langlands.Automorphic.cuspidalArchimedeanGenericComponentBridge` (module
`Langlands.Automorphic.CuspidalArchimedeanGenericComponentReduction`) proves
`CuspidalArchimedeanIrreducibleAdmissibleComponentStatement →
CuspidalArchimedeanWhittakerFunctionalStatement → CuspidalArchimedeanGenericComponentStatement`.
The proof applies it to
- `cuspidalArchimedeanIrreducibleAdmissibleComponent` (module
  `Langlands.Automorphic.PlaceComponentExistence`): at every infinite place, an actual cuspidal
  realization has a subspace that is irreducible for the place actions and admissible for the
  compact group; and
- `cuspidalArchimedeanWhittakerFunctional` (module
  `Langlands.Automorphic.CuspidalWhittaker.PlaceWhittaker`): every nonzero subspace stable
  under the place actions at an infinite place carries a Whittaker functional for some
  nondegenerate character that is nonzero on it (from the Whittaker–Fourier expansion of cusp
  forms).

The result says that at every infinite place `v`, `T.realization` contains, through an
injective intertwining map `ι`, an irreducible admissible generic `(𝔤, K)`-module of the
type of `v`.

Inside `cuspidalArchimedeanParameterReduction`, the local input gives this module an injective
intertwining map from a standard module. Composing it with `ι`
(`OperatorRealization.hasRealPlaceParameter_of_component` at a real place,
`OperatorRealization.hasComplexPlaceParameter_of_component` at a complex place) gives the
parameter of `T.realization` at `v`.

## Check

A private `lean_check` of this module, with the declaration inspected, reported 0 errors and
0 warnings. The theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

Provenance: *derived*. The statement is the published
`CuspidalArchimedeanParameterExistenceStatement`. For its sources, see
`CuspidalPairFunctionalEquationReduction.md` and `ArchimedeanParameterReduction.md`. The proof
composes only Library theorems. Their mathematical sources are documented in their own
Markdown:
- the Langlands classification of `GL_n(ℝ)` (Knapp 1994) and Casselman's theorem for the real
  classification step;
- Kostant (1978) and Vogan (1978) for the injectivity of generic Langlands quotient maps
  (`RealGenericLargeReduction.md`), and for `complexGenericStandardParameter`;
- the Whittaker–Fourier expansion and the admissibility of the place components for the global
  generic-component theorems.
