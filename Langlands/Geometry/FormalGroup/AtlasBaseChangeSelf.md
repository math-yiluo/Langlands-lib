# Actual formal comparison for identity coefficient extension

For an actual formal O-module atlas X over R, `baseIdIso` is a formal
isomorphism from `X.baseChangeAlong (AlgHom.id O R)` to X. Both of its maps use
identity coordinate series on every test. Its evaluation agrees with the
existing identity coefficient-extension comparison on entire compatible
families, in both directions.

## Scope and provenance

O and R are arbitrary commutative rings with a supplied O-algebra structure
on R. R and its tests have universe v; entire compatible families have
universe v+1. The coordinate type is finite. The principal cover may be
infinite. There are no noetherian, flatness or nontriviality hypotheses.

This is internal infrastructure derived from `AtlasBaseChangeAlong`,
`AtlasAlgebraTransport`, actual coefficient extension and the atlas
naturality laws. It asserts no additional result from the literature. The
localization-gluing convention inherited from the original atlas is
documented in `BasicAtlas.md`.

The result compares identity coefficient extension of an atlas with that
same atlas. It supplies actual formal maps, their inverse equations and
their complete-family squares. Full-order actions, specialness, height,
classes of presentations, coherence for arbitrary successive supplied
coefficient maps, framing and representability remain separate.

All declarations below are in
`Langlands.FormalGroup.ModuleLaw.BasicAtlas`.

## Cover, coefficients and chart laws

`baseIdOpens_eq` proves equality of the extended and original principal
generators by the image-of-identity equality for sets. `baseIdSource` is the
original chart chosen by coefficient extension above an original generator.
`baseIdSource_eq` proves that it equals that original chart, using the
chosen-source image equation and subtype extensionality.
`baseIdSource_unit` transfers the generator's invertibility.

`baseIdChartRingHom` is the underlying ring homomorphism of the actual
localization coefficient map in the identity extension.
`baseIdChartRingHom_algebraMap` identifies its value on every coefficient
from R. `baseIdCoefficient_comp` proves that composing this map with
localization into a test A equals the original localization map into A.
The proof uses uniqueness of ring homomorphisms from a localization and
their values on R.

`baseIdChartIso` compares the extended and original chart laws on A by
identity coordinates. Equality of the addition series and of every
O-action series follows by associating the two coefficient maps, applying
`baseIdCoefficient_comp`, and reindexing along `baseIdSource_eq`.
This compares the actual formal laws and actions.

`identityTestHom A` is the identity ring map from
`restrictCoefficientAlgebra (AlgHom.id O R) A` to A;
`identityTestInv A` is the identity ring map in the other direction. Each
checks R-linearity by reflexivity. Keeping these bundled tests explicit
avoids assuming their scalar-structure presentations are definitionally equal.

## Formal transitions and inverse maps

`baseIdTransition_coordinates` identifies the entire forward transition
series on every test with the original transition series at the matching
indices. First scalar-structure transport retains the raw extended series.
The raw extension has the original transition at its chosen original
indices on the restricted test. Naturality along `identityTestHom A`
identifies that series with the original one on A; mapping a series along
the identity ring map leaves it unchanged. Finally `baseIdSource_eq`
reindexes both chart choices.

`baseIdHom` uses the forward maps of `baseIdChartIso`.
`baseIdInv` uses their inverse maps, with chart indices transported across
the reverse cover equality. Their coefficient naturality follows from
preservation of the identity coordinate map. Their transition squares
follow from `baseIdTransition_coordinates` and the two identity
composition laws for coordinate maps.

`baseIdIso` retains exactly these two formal maps. Both formal inverse
equations are proved by extensionality on every test chart: the composite
coordinate series is the identity composed with itself.

## Complete-family squares

`baseIdPointEquiv_component` identifies every tuple in the previously
constructed `baseChangeAlongPointEquiv` with its selected original chart
on the identity-restricted coefficient test. It uses the full-family
scalar-transport component equation and the coefficient-extension
component definition.

For every R-test A and every complete compatible family
`x : X.Point (restrictCoefficientAlgebra (AlgHom.id O R) A)`,
`baseId_onPoints` proves

```text
X.baseIdIso.onPoints A
  (X.baseChangeAlongPointEquiv (AlgHom.id O R) A x)
  = X.mapPoints (identityTestHom A) x.
```

The proof works component by component over every further coefficient
test. It removes evaluation of the identity series, applies
`baseIdPointEquiv_component`, and uses the family's coefficient naturality
under `identityTestHom` of the further test. The identity ring map leaves
the tuple unchanged. Equality of the chosen and original chart indices
then identifies the final components.

`baseId_inv_onPoints` gives the reverse square:

```text
(X.baseIdIso.onPoints A).symm
  (X.mapPoints (identityTestHom A) x)
  = X.baseChangeAlongPointEquiv (AlgHom.id O R) A x.
```

It follows from the forward square by the inverse law of the linear
equivalence induced by the actual formal isomorphism.
