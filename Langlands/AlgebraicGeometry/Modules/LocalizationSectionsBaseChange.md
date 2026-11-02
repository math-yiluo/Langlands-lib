# Sections localization from scalar base change

This derived helper uses the existing ordinary and scalar sections comparisons
for an arbitrary commuting square of schemes above `Spec R` and `Spec T`.
The square is not required to be Cartesian.

`scalarSectionsBaseChangeAlgebraEquiv` assumes that `T` is an `R`-algebra
and that the specified `scalarSectionsBaseChangeMap` is invertible. It converts
that map into a `T`-linear equivalence from the ordinary algebra tensor product
`T tensor_R relativeGlobalSections(f,M)` to the relative sections of the actual
pullback. The conversion uses `extendScalarsAlgebraEquiv` from `TildePullback`:
categorical scalar extension and the ordinary tensor product have different
presentations of the scalar action and are connected by that explicit equivalence.

`isLocalizedModule_sectionsBaseChangeMap` adds a submonoid `S` of `R` and
`IsLocalization S T`. It proves that the specified ordinary sections map is a
localization of modules at `S`. The proof restricts the preceding equivalence
to an `R`-linear equivalence with the actual restricted-scalars target, transports
Mathlib's localization property of `m` mapping to `1 tensor m`, and identifies
the composite with the ordinary sections map by the published generator formula
`scalarSectionsBaseChangeMap_one_tmul`. It does not assume or conclude
quasi-coherence of a direct image.

`pullback_unit_app_comp_restrictFunctorIsoPullback_inv` computes the actual
pullback unit for an open immersion `j`. After applying the inverse of the
canonical restriction-to-pullback isomorphism, its component on any open `W`
is the ordinary restriction to `j(image of inverse image of W)`. The proof
first uses uniqueness of left adjoints to compare the two adjunction units,
cancels the restriction-to-pullback isomorphism as a morphism of sheaves, and
then takes the section component.

The provenance is internal and derived: the constructions use
`CohomologyBaseChangeZero`, `SectionsBaseChangeComposition`, `TildePullback`,
and Mathlib's localization-of-modules and open-restriction adjunction APIs.
No new geometric or external-source result is asserted. These are supporting
lemmas for the direct-image task; they do not establish its rank, local freeness,
or arbitrary base-change conclusion.
