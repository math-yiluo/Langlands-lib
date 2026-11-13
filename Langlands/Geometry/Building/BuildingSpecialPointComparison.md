# Specialness in a building and its defining apartment

This internal lemma compares the existing definitions in `KPBuilding` and
`AffineRootSystem`. It applies over any field and to every `KPApartmentData`,
without V 6 or apartment axioms.

`KPApartmentData.isSpecialBuildingPoint_apartmentMap_iff` states that an
apartment point is special exactly when its image in the reduced building
is a special building point. For the forward implication, the definition of
`IsSpecialBuildingPoint` supplies a translate of a special apartment point
with the same building image. `ApartmentQuotient.mk_eq_mk_iff` supplies a
normalizer element carrying that point to the original apartment point.
`normalizerAffineEquiv_mem_rootStabilizer` and
`AffineRootSystem.isSpecialPoint_apply_iff` transport specialness along
that normalizer element. The reverse implication is the existing
`isSpecialBuildingPoint_apartmentMap`.

The provenance is these published Library definitions and theorems. This
lemma supplies the building-to-apartment step of the proof of KP
Proposition 9.9.2. Descent between apartments for different tori and fields
is a separate assertion and is not proved here.

`BuildingSpecialPointComparisonStatement` universally quantifies this
comparison over fields, tori, affine groups, monomorphic torus maps,
orders, apartment data and points in universe `u`.
`buildingSpecialPointComparison` proves it by applying the lemma above.
This is an internal comparison, not a replacement for the published
unramified descent statement.
