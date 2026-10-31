# Derived base change on the explicit complex of sections

This internal extension transports `DerivedBaseChangeResolution` to the
complex obtained by first taking sections and then extending from
natural to integer degrees. All schemes and rings have the same
arbitrary universe `u`.

For a right resolution `ε : M[0] ⟶ K`,
`resolutionSectionsDerivedComparison` is the canonical morphism from
the localization of the extended sections complex to actual derived
relative sections. It applies `Q` to the published `mapExtendIso` and
then uses `derivedResolutionComparison`. No acyclicity of sections
of the terms is needed to define it.

For any ring map `φ : R ⟶ S`, `sectionsRestrictScalarsIso` identifies
scalar restriction of the localization of an extended `S`-complex with
the localization of its extended scalar restriction. Its specified
composite uses `mapDerivedCategoryFactors` and `extendMapIso`.

Given a commuting scheme square and a cochain map `t : K ⟶ g_*L`,
`derivedSectionsBaseChangeMap` localizes the integer extension of
the actual `resolutionSectionsBaseChangeMap` and then applies the
inverse of `sectionsRestrictScalarsIso`.
`derivedSectionsBaseChangeMap_comparison` identifies this map with
`derivedResolutionBaseChangeMap` through the specified extension
comparisons on source and target.

For compatible augmentation quasi-isomorphisms of `M` and `g^*M`,
with the pushforward augmentation also a quasi-isomorphism and
vanishing positive higher direct images of `g^*M`,
`resolutionSectionsDerivedComparison_baseChangeMap` intertwines the
explicit sections map and the published `derivedBaseChangeMap`.
No flatness of `φ`, Cartesian-square assumption, or term acyclicity
for sections is required.

The implemented transport proof uses naturality of `mapExtendIso`,
cancels the three factors in `compResolutionIso`, and inverts the
published composite-extension coherence identity. It expands the
exact-postcomposition comparison using
`resolutionPostcompNatIso_hom_app_comp_resolutionCongrNatIso_hom_app`
and moves the extension comparison past `mapDerivedCategoryFactors`
by naturality. The final equality follows from
`derivedResolutionComparison_baseChangeMap`.
Thus the argument compares the actual derived morphisms, retaining
every extension and localization isomorphism.

The provenance is internal: the definitions and equalities are
transports of published constructions and the preceding resolution
compatibility theorem. No external theorem is restated. This file
does not assert invertibility of base change or the relative cube
theorem.
