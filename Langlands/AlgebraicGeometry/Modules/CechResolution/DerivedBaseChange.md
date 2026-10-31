# Actual derived base change through alternating Čech cochains

This internal extension of the canonical derived Čech comparison works
over any homomorphism `φ : R ⟶ S` of commutative rings in an arbitrary
universe `u`. For a commuting square with an affine morphism `g : Y ⟶ X`,
it uses the full inverse-image ordered affine cover on `Y`.

For an actual coefficient morphism `a : M ⟶ g_*N`,
`scalarCechCochainMap` is the specified `scalarCechSectionsMap`
transported by `sectionsComplexIso` on its source and target.
`cechCochainSectionsMap` transports the semilinear
`resolutionSectionsBaseChangeMap` by the same isomorphisms.
`cechCochainSectionsMap_eq_adjunct` proves that these are actual
adjuncts under extension and restriction of scalars on complexes.
Neither construction assumes flatness or a Cartesian square.

For the pullback/pushforward adjunction unit,
`cechDerivedBaseChangeMap` applies `Q` to the integer extension of
this semilinear alternating-cochain map and then uses the inverse of
the specified `sectionsRestrictScalarsIso`.
`cechDerivedBaseChangeMap_eq_transport` identifies this precise
morphism with `derivedSectionsBaseChangeMap` transported by the
two sections-complex isomorphisms.

Assume that all positive higher direct images under `g` of `g^*M`
vanish. `cechSectionsDerivedComparison_baseChange` proves that the
canonical Čech sections comparisons intertwine the actual cochain
sections map and the actual `derivedBaseChangeMap`.
`cechDerivedComparison_baseChange` gives the same equality for the
named canonical comparison from alternating Čech cochains.
These are equalities of actual derived-category morphisms, with all
extension, localization, and scalar-restriction comparisons retained.
The statements do not assume separatedness or quasi-coherence:
their conclusions assert compatibility, not invertibility.

The implemented proof specializes
`resolutionSectionsDerivedComparison_baseChangeMap` to `cechAug`
and `cechPullback`. The published augmentation theorem gives both
Čech quasi-isomorphisms, and `quasiIso_pushforward_cechAug` gives
the pushed-forward augmentation quasi-isomorphism. The actual
augmentation square is `cechAug_cechPullback`.
Naturality of `mapExtendIso` and `mapDerivedCategoryFactors`
establishes the scalar-restriction transport. Functoriality of
extension and localization and cancellation of `sectionsComplexIso`
then give the alternating-cochain equality. The adjunct identity
uses naturality of the scalar adjunction.

The provenance is internal: these constructions expose and compare
the existing specified maps, using the preceding generic resolution
and sections compatibility results. No external theorem is restated.
This file does not assert derived scalar-extension invertibility,
the existence of a perfect representative, or the relative cube theorem.
