# The maximal-unramified specialization of apartment injection

This module proves the existing
`Langlands.Geometry.Building.MaximalUnramifiedApartmentInjectiveStatement`.
For a nonarchimedean local field `F`, a group `H` over
`Spec (inertiaFixedField F)` and supplied
`C : MaximalUnramified.BuildingData F H`, the map `C.apartmentMap` is
`C.apartment.apartmentMap`. The theorem
`maximalUnramifiedApartmentInjective` applies the general
`KPApartmentData.apartmentMap_injective` to `C.isConnectedReductive` and
`C.isMaximalSplitTorus`.

The two general arbitrary-field lemmas previously in this module,
`KPApartmentData.normalizer_smul_eq_self_of_mem_sharpFixer` and
`KPApartmentData.apartmentMap_injective`, now live in
`GenericApartmentInjection` with their names and proofs unchanged. That paired
module explains the normalizer and generic point-exchange proof in full. This
internal refactoring preserves the published wrapper theorem and every general
declaration. The present module still imports
`UnramifiedBuildingDescentReduction` for the wrapper's statement definition;
the general module has no such dependency.

The generic injection works in arbitrary universes and both characteristics,
with no local-field or apartment-axiom premise. In the present specialization,
the quasi-split structure over the maximal unramified field, full V6 and the
valuation normalization are not used by the proof. This specialization is one
input of the descent reduction and does not by itself prove that reduction or
locate a prescribed Galois-fixed point in a special apartment.
