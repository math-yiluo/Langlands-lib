# The actual coinduced model of the separate smooth Godement functor

This module constructs a natural comparison for the existing separate smooth
Godement degree-zero functor and proves compatibility with its actual
coaugmentation. It imports [Smooth](Smooth.md),
[Underlying](Underlying.md) through that module, and
[coinduced-family functoriality](../CoinducedFamilies/Functoriality.md).
These imported constructions are unchanged.

## Scope and notation

The commutative ring `R`, group `G`, space `X`, and module carriers belong to one
arbitrary universe `u`. The group has a topology and `IsTopologicalGroup G`.
The space has a `G`-action with `ContinuousConstSMul G X` and
`HasStableNeighbourhoods G X`, as required by the existing smooth coreflector.
All sheaves here are module sheaves on the ordinary-open transport category;
its restriction to ordinary opens satisfies the ordinary sheaf condition.

Write `I` for `smoothInclusion`, `U` for `toSheaf`, `C` for actual right Kan
`coinduction`, and `S` for `smoothCoreflector`. Write `Z` for the existing full
equivariant `zeroFunctor` and `z` for the ordinary Godement degree-zero functor
over all points of `X`. The imported separate `smoothZeroFunctor` is
`I ⋙ U ⋙ z ⋙ C ⋙ S`. The imported `coinducedZeroFunctor` is
`Q = Z ⋙ U ⋙ C`. In particular the comparison below retains actual coinduction
before taking the smooth part.

## The natural comparison

`smoothZeroCoinducedIso` has type

```text
smoothZeroFunctor R G X ≅ I ⋙ Q ⋙ S.
```

The existing `zeroIso` is the natural isomorphism `Z ⋙ U ≅ U ⋙ z`.
Whisker its inverse on the right by `smoothCoinduction = C ⋙ S` and on the left
by `I`. This constructs the displayed isomorphism with its naturality and inverse
laws. No comparison is supplied as a hypothesis.

The component formulas `smoothZeroCoinducedIso_hom_app` and
`smoothZeroCoinducedIso_inv_app` identify the forward component at a smooth
sheaf `F` with `S.map (C.map (zeroIso.inv.app F.obj))` and the inverse component
with `S.map (C.map (zeroIso.hom.app F.obj))`. Both equalities are definitional.

## Actual coaugmentations

Let `etaS` be the unit of `I ⊣ S` and `aQ` the actual coinduced coaugmentation
from the imported functoriality module. Define
`coinducedSmoothCoaugmentation : 𝟭 ⟶ I ⋙ Q ⋙ S` at `F` by

```text
etaS_F ≫ S.map (aQ_(I F)).
```

`coinducedSmoothCoaugmentation_app` identifies this component with the actual
adjoint of `aQ_(I F)` under `I ⊣ S`.
`coinducedSmoothCoaugmentation_inclusion` proves that applying `I` and then
the actual smooth-subsheaf inclusion into `Q(I F)` recovers precisely
`aQ_(I F)`. The proof uses the adjunction hom equivalence and its counit formula.

`coinducedSmoothCoaugmentation_comparison` proves that this coaugmentation
followed by the inverse comparison is the original `smoothCoaugmentation`.
Expand `aQ` as the original equivariant germ map followed by the coinduction
unit. Naturality of that unit moves the germ map inside `C`. The imported
`zeroIso_comm` identifies the resulting ordinary morphism with the ordinary
Godement coaugmentation. The composite-adjunction unit formula then gives
exactly the defining formula for the original smooth coaugmentation.

`smoothCoaugmentation_coinducedIso` gives the forward equation

```text
smoothCoaugmentation.app F ≫ smoothZeroCoinducedIso.hom.app F
  = coinducedSmoothCoaugmentation.app F.
```

It follows by composing the inverse equation with the forward isomorphism and
using the inverse-hom identity. Both compatibility equations and the inclusion
equation have reassociated versions.

## Provenance and remaining scope

This is an internal construction from the actual imported functors, natural
isomorphism, units, counit, and proved germ-compatibility equation. It introduces
no additional literature assertion or unproved mathematical premise. It supplies
a degree-zero comparison for use in subsequent smooth spatial constructions.
It does not construct a spatial map or a comparison of higher smooth complexes,
and it proves no exactness, acyclicity, derived comparison, or analytic, etale,
arithmetic, or Shimura specialization. Those remain separate obligations of
the broader framework.
