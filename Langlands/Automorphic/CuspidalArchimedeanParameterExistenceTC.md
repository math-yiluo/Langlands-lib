# Archimedean parameters of cuspidal realizations over totally complex fields

The module proves `Langlands.Global.CuspidalArchimedeanParameterExistenceTCStatement`
(module `Langlands.Global.Factors.CuspidalPairFunctionalEquationTCStatement`). The theorem is
`Langlands.Automorphic.cuspidalArchimedeanParameterExistenceTC`.

## Statement proved

Let `F` be a totally complex number field with compact adele quotient, let `r : ℕ`, and let
`T` be an actual cuspidal realization of `GL_{r+1}` over `F`. The statement has two clauses:

1. every real place `v` has a list `ds` of real blocks with
   `OperatorRealization.HasRealPlaceParameter T.realization v ds`;
2. every complex place `v` has a list `ds` of complex characters with
   `OperatorRealization.HasComplexPlaceParameter T.realization v ds`. That is, the
   `U(r+1)`-finite part of the standard module of `ds` embeds injectively into the space of
   `T.realization`, intertwining the compact and Lie actions at `v`.

The theorem has no hypotheses. Each clause is proved as stated.

## Proof

Fix `F`, `r` and `T`.

- **Real places.** A real place `v` satisfies `v.IsReal`. Since `F` is totally complex,
  `NumberField.IsTotallyComplex.isComplex v` gives `v.IsComplex`. Mathlib's
  `NumberField.InfinitePlace.not_isReal_iff_isComplex` turns this into `¬ v.IsReal`. So
  there are no real places and the first clause is vacuous (`absurd`).
- **Complex places.** Three published Library theorems are combined:
  - `cuspidalArchimedeanGenericComponentBridge`
    (`Langlands.Automorphic.CuspidalArchimedeanGenericComponentReduction`), applied to
    `cuspidalArchimedeanIrreducibleAdmissibleComponent`
    (`Langlands.Automorphic.PlaceComponentExistence`) and
    `cuspidalArchimedeanWhittakerFunctional`
    (`Langlands.Automorphic.CuspidalWhittaker.PlaceWhittaker`). Together they prove the
    global premise `CuspidalArchimedeanGenericComponentStatement`. Its complex-place half
    gives an irreducible admissible generic `(𝔤𝔩_{r+1}(ℂ), U(r+1))`-module `V`, with actions
    `ρ` and `π`, and an injective map `ι : V → T` that intertwines the compact and Lie
    actions at `v`.
  - `Archimedean.complexGenericStandardParameter`
    (`Langlands.Representation.Archimedean.ComplexGenericStandardParameterProof`) proves
    `ComplexGenericStandardParameterStatement`. Applied to `V`, it gives a list `ds` of complex
    characters with `HasComplexStandardParameter (r+1) ρ π ds`: the `U(r+1)`-finite part of
    the standard module of `ds` embeds injectively and equivariantly into `V`.
  - `OperatorRealization.hasComplexPlaceParameter_of_component`
    (`Langlands.Automorphic.ArchimedeanParameterReduction`) composes the two embeddings and
    gives `HasComplexPlaceParameter T.realization v ds`.

This argument is the complex half of the Library reduction `cuspidalArchimedeanParameterReduction`
for the general target `CuspidalArchimedeanParameterExistenceStatement`. The real local premise
`RealGenericStandardParameterStatement` is not needed, because a totally complex field has no
real places.

## Lean notes

The module turns on `LieRing.ofAssociativeRing` as a local instance of priority 100 and sets
`backward.isDefEq.respectTransparency false`, as the imported place-component modules do, so
that the Lie-action types of the bridge and of the local statement unify.
