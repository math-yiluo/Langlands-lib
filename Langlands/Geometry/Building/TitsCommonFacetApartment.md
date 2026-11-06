# Common original apartments from the Tits comparison

Let `P` be supplied actual `ParahoricBuildingData G` over any nonarchimedean
local field `F : Type u`. Fix `Ca`, a group `W : Type u`, the homomorphism
`π : P.normalizerInZero →* W`, and `Sgen`, and assume the full existing
`hT : P.IsBuildingTitsSystem Ca π Sgen`. All subsets, facets, apartments and
actions in this module are those of the existing quotient `P.ReducedBuilding`.

`exists_apartment_contains_facets` proves that any two original building
facets are contained in a common translated apartment. The proof uses the
surjective and injective parts of the supplied facet–stabilizer bijection and
the supplied equality of apartment families, together with the Tits axioms.
It does not require apartment axioms, chart injectivity, a geometric building,
or a polysimplicial realization as an additional premise.

The implementation sends the two facets to their admissible parabolic
stabilizers and applies `IsTitsSystem.exists_common_restrictedApartment`.
The apartment-family equality then represents this restricted apartment by
the stabilizers of all facets contained in an actual translate `g • A(S)`.
For each original facet, image membership supplies a facet contained in
that translate with the same stabilizer. Injectivity of the stabilizer map
identifies it with the original facet, proving containment of both originals.
No identification of the distinguished apartments is needed.

`commonFacetApartment` chooses one such subset of the original quotient;
`commonFacetApartment_spec` records its apartment property and both
containments. `exists_apartment_mem_mem` chooses existing facets containing
two arbitrary points and puts these facets in a common apartment.
`hasCommonApartmentWith` supplies the Library's corresponding predicate.
Existence of a containing facet uses the original quotient representatives
and affine-root facets; it needs neither a partition-uniqueness premise nor
a geometric building axiom.

For any supplied `P.toValuationBuildingData.PolysimplicialRealization R`,
`realization_exists_apartment_facets` puts every two complex facets in one
member of the existing family `R.apartments`. It uses only their realized
building facets and the definition of `R.apartmentComplex`.
`realization_exists_apartment` restricts to chambers, giving exactly the
`exists_apartment` field of `AbstractBuilding.IsBuilding`, namely BL3.
These two theorems do not require `R.IsFaceCompatible`: only the supplied
bijection of facets is used.

The provenance is internal: the existing `FullValidity.ChamberAxioms` Tits
comparison, `TitsFacetApartmentTransport` apartment conventions,
`CommonApartmentConstruction.exists_buildingFacet_mem`, the existing
realization definitions, and the Bruhat deduction in `TitsCommonApartment`.
This module introduces no new external assertion. The full Tits comparison
and actual data remain premises, and its existence is not proved here.
The module does not construct a realization, prove BL1 or BL2, construct a
polysimplicial vertex action, or prove the unconditional
`RootValuationBuildingConstructionStatement`.
