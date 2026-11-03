# Actual Picard pullback and unit cohomology for nilpotent immersions

This internal construction combines the published actual homeomorphism
comparison, coefficient naturality, ordered-unit pullback and line-bundle
classification. It adds no external mathematical input and works at arbitrary
universe `u`.

For any nilpotent closed immersion `i : Y ⟶ X`, `cohomologyMap` is the map on
actual unit-sheaf cohomology induced by the actual structure-unit reduction,
followed by the exact published nilpotent homeomorphism equivalence. It is
defined in every degree. `cohomologyMap_squareZero` identifies it with the
existing `SquareZeroUnitCohomology.reductionMap` for a square-zero immersion.

For a nilpotent closed immersion and a finite full open cover,
`classOfCocycle_pullback` identifies the actual H¹ class of the pulled unit
cocycle with the coefficient map of actual units followed by the published
homeomorphism cohomology equivalence. The proof composes the published
`comparisonHom_pushforward` with `comparisonHom_naturality`. This identity
requires no compactness assumption on either scheme.

For compact schemes, `Group.unitCohomologyClass_pullback` represents an arbitrary
Picard class by the gluing of a chosen finite presentation. The actual gluing
pullback theorem and the presentation-independent classifier reduce the result
to the preceding cocycle identity. `unitCohomologyAddEquiv_pullback` states the
same identity using the published additive equivalence.
`unitCohomologyClass_pullback_squareZero` specializes to the existing
square-zero cohomology reduction map.

The Picard-class and additive-classifier identities assume compactness of
both underlying scheme spaces, as required by the existing classification.
They impose neither properness, smoothness, separatedness nor a ground-field
hypothesis. The closed immersion need only have nilpotent kernel; it need not
split. Provenance is the internal composition of `AbelianSheafH1Pushforward`,
`AbelianSheafH1Naturality`, `UnitCechPullback`,
`UnitH1LineBundleClassification`, `UnitH1AddEquiv` and
`SquareZeroUnitCohomology`. No cohomology theory, Picard group or classifier is
replaced. Line-bundle obstruction and deformation results and the final fppf
Picard representability target remain separate obligations.
