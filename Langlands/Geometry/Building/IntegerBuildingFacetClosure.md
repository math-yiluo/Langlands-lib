# Closed facets in the integer-valued building over arbitrary fields

`IntegerBuildingFacetClosureStatement` concerns every field `k : Type u`,
integer-valued valuation `v`, affine group scheme `G` over `k`, and supplied
`B : IntegerValuationBuildingData v G`. For every rational point `g` of `G`
and apartment point `a`, it asserts

```text
buildingFacetClosure (buildingFacetAt (translatedApartmentMap g a))
  = translatedApartmentMap g '' facetClosure B.affineRoots a.
```

The statement has no characteristic, local-field, topology, chart-injectivity,
or apartment-axiom hypothesis. The supplied building data retain their existing
connected reductivity, maximal split torus, KP apartment and integer-valuation
compatibility assumptions. This module asserts no existence of those data.

All sets lie in the original `B.ReducedBuilding` with its original `G(k)`
action. `apartmentImage` is the range of the original apartment map, and
`translatedApartmentMap g a` is `g • B.apartmentMap a`. `BuildingFacet` and
`buildingFacetAt` come from `IntegerBuildingFacetPartition`: they are the
original full-facet subsets and their unique containing-facet map.

`FacetPrecedes F C` means that one translated original apartment presents
`F` and `C` as the images of affine facets satisfying the existing
`AffineRootSystem.IsFaceOf` relation. It includes equality.
`buildingFacetClosure C` is the union of all full facets `F` with
`FacetPrecedes F C`. The theorem identifies that union with the image of the
existing affine-root closed-side formula in every presentation of `C`.
No topological closure on the quotient is asserted.

## Implemented proof

The original quotient relation turns an equality
`g • apartmentMap a = apartmentMap b` into a normalizer element `n` such that
`n • a = b` and `g⁻¹ n` belongs to the sharp fixer at `a`. The generic theorem
`KPApartmentData.sharpFixer_singleton_le_of_mem_facetClosure`, imported from
`BuildingFacetIncidence`, puts that same element in the sharp fixer at every
point of the affine-root closure of `a`. It needs only AS4, which
`IntegerBuildingFacetPartition.affineRoot_mem_or_two_smul_mem` derives from
actual rank-one factorization for the supplied connected reductive group.
The sharp-fixer action and normalizer equivariance therefore give
`g • apartmentMap y = apartmentMap (n • y)` throughout this closed facet.
This is `exists_normalizer_eq_on_translated_facetClosure`.

The actual normalizer preserves ordinary affine roots by
`KPApartmentData.normalizerAffineEquiv_mem_rootStabilizer`, whose signature
requires no AS5 premise. Applying `AffineRootSystem.IsFaceOf.image` proves
`normalizer_smul_isFaceOf`. If an apartment contains an upper facet, choose
coordinates there for an upper representative from an incidence witness.
The closed-facet coordinate change just proved agrees on both the lower and
upper affine facets. Their images in the chosen apartment are still incident.
This proves `exists_apartment_faces_of_facetPrecedes` and
`subset_apartment_of_facetPrecedes` without chart injectivity.

For the closure formula, take a lower facet in the defining union and a chart
witnessing its incidence with `C`. An arbitrary prescribed representative
`a` of `C` has coordinates `c` in that chart. Change coordinates from `c`
to `a` using the preceding normalizer. Every lower point lies in the
closed facet of `c` by `KPApartmentData.mem_facetClosure_of_isFaceOf`;
root preservation puts its changed coordinates in the closed facet of `a`.
This proves one inclusion. Conversely, if `y` is in the affine-root closure
of `a`, the full affine facet through `y` is a face of the facet through
`a`, by `AffineRootSystem.facet_subset_facetClosure_iff`. Its translated
image is one of the lower full facets in the union. Thus
`buildingFacetClosure_eq_image` holds in any presentation of `C`.

The existing full-facet partition identifies the facet through
`translatedApartmentMap g a` with the image of the full affine facet through
`a`. Substituting this equality gives the entry statement and the theorem
`integerBuildingFacetClosure`.

The partition also proves that a point is in a closed facet exactly when its
unique containing facet precedes that facet. Consequently, one point of a
full facet in the closed facet implies the entire face incidence, and
incidence is equivalent to containment of that full facet in the closed
facet. Every apartment containing `C` contains its entire combinatorial
closure.

## Provenance and remaining scope

This is an internal extension of the published local-field deductions in
`BuildingFacetIncidence` and `BuildingFacetClosure` to the existing
integer-valued data over arbitrary fields. Its inputs are the original
`ApartmentQuotient` relation, `IntegerValuationBuildingData`,
`IntegerBuildingFacetPartition`, the generic affine-root face and closure
lemmas in `BuildingFacetIncidence` and `ChamberFiltration`, and actual
normalizer root preservation from `NormalizerAffineRootAction`. The
local-field full-apartment-axiom premises are discharged where used by the
derived AS4 theorem and the unconditional normalizer root theorem.
No additional external source assertion is introduced.

The auxiliary `facetPrecedes_iff_isFaceOf` reflects incidence into
*prescribed* common coordinate sets under the explicit premise
`Function.Injective B.apartmentMap`. This module does not prove that premise
for arbitrary-field integer-valued data, and it does not claim a partial order
or an injective closed-facet map without it. The unconditional common-chart
transport and closure formula above do not use that premise.

This focused prerequisite constructs no descended facet-model family,
Galois-facet/parabolic correspondence, residue-torus lifting or prescribed-point
special apartment. The main `UnramifiedFixedPointSplitTorusStatement` remains
an additional obligation.
