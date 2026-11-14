# Reduction of the ordered integral open cell to two torus inputs

Module `Langlands.BruhatTits.IntegralModels.OrderedIntegralOpenCellReduction`.

## Statement

`UnramifiedOrderedIntegralOpenCellReductionStatement.{u}` is the implication

```text
UnramifiedTorusConnectedBoundStatement.{u} →
UnramifiedTorusIwahoriConnectedImageStatement.{u} →
UnramifiedOrderedIntegralOpenCellStatement.{u}
```

between three published propositions, all unchanged:

1. `UnramifiedTorusConnectedBoundStatement` (KP Corollary B.8.7 with the argument
   of Proposition B.8.8(3)): for a torus over `K = inertiaFixedField F` split by a
   finite Galois `L`, every smooth model over `O = fixedFieldIntegers F` with
   geometrically connected fibres has integral points inside the norm-defined
   Iwahori subgroup `T(K)^0`.
2. `UnramifiedTorusIwahoriConnectedImageStatement` (KP Lemma B.3.1 and
   Definition 2.5.13): `T(K)^0` is the image of the integral points of a smooth
   model with geometrically connected fibres under a homomorphism of `K`-groups.
3. The target `UnramifiedOrderedIntegralOpenCellStatement` of Task 6495: KP
   Proposition 8.3.14(3), open-immersion clause, with family existence, over `K`
   and `O`, for compatible centralizer data and every smooth model with the exact
   zero-point fixer.

Neither input is proved in this contribution; both are the unproved inputs of the
published `UnramifiedTorusIwahoriModelAssemblyStatement` (Task 6162). This module
does not prove the target unconditionally.

## Implemented proof

`unramifiedOrderedIntegralOpenCellReduction` proves the implication. Given the
data of the target, `exists_integralSplitTorusData` gives an actual closed integral
split torus `T` of `N` with generic torus `C.i`. The proved
`RelativeIdentityComponent.smoothExistence` gives a smooth geometrically
connected relative identity component of the published integral centralizer model
of `T` (with the specified generic representative `E.i`). Geometric connectedness
of `E.T` follows from its splitting over `L`
(`geometricallyConnected_of_isSplitTorus_baseChanged`). Under the two inputs,
`neutralCentralizer_integralPoints_eq` identifies the integral points of this
identity component with `E.torusIwahori`, so `family` is an actual
`TorusRootModelFamilyData C E x Ω N`. The proved `isOpenImmersion_family` gives
the open immersion for every generic cocharacter and every pair of injective
enumerations with the prescribed ranges, including empty ones.

## Provenance

The entry proposition is an internal reduction (derived provenance) of the
published target, isolating exactly the torus inputs of KP's argument: the source
uses the connected Néron model `T⁰` with `T⁰(O) = T(K)⁰` (Corollary B.8.7) in the
proofs of Proposition 8.2.4, Theorem 8.3.13 and Proposition 8.3.14, printed
pp. 289–290 and 299–300 / PDF pp. 320–321 and 330–331
(`kaletha-prasad-2023-bruhat-tits-new-approach`). Everything else, including the
integral open cell and the root-group comparisons, is proved in the supporting
modules `IntegralPointIsoCriterion`, `GenericOrderedFixerFactors`,
`OrderedCellLemmas`, `OrderedIntegralOpenCellFamily` and
`OrderedIntegralOpenCellProof`, whose Markdown describes the implemented route
and its differences from the source.
