# Intersections of original closed facets in the valuation quotient

All objects in this file use the existing reduced valuation quotient, its
original rational-point action, the existing facets and the combinatorial closed
facets defined as the unions of their incident lower facets. Work over an
arbitrary field universe with the existing nonarchimedean local field structures.
The actual valuation or parahoric building data are supplied.

For supplied full apartment axioms and an injective original apartment map,
`buildingFacetClosure_inter_nonempty_iff_vertexFinset_inter_nonempty` says that
two original closed quotient facets meet exactly when their original vertex
finsets intersect. A point in the intersection determines an original facet
incident to both input facets. Every actual vertex of that facet belongs to
both closed facets. The converse follows from the exact original-vertex
membership criterion. This theorem needs no global common-apartment comparison.

`exists_buildingFacetClosure_eq_inter_in_chart` proves that a nonempty
intersection of two closed facets presented in a common original chart is
another original closed quotient facet. Chart injectivity identifies the
intersection of the images with the image of the intersection. The affine
intersection theorem presents that intersection as the original closed facet
of the centroid of the common actual affine vertices. The exact chart formula
for original quotient closed facets then gives the desired quotient facet.
`exists_buildingFacetClosure_eq_inter_of_common_apartment` uses the existing
facet-presentation theorem to obtain the same result from containment in a
common original apartment.

The declarations in `ParahoricBuildingData.IsBuildingTitsSystem` additionally
assume the existing full actual Tits comparison. Its common-apartment theorem
supplies a common original apartment for every pair of facets, without assuming
a geometric building realization. Thus
`exists_buildingFacetClosure_eq_inter` applies globally.
`closedFacetIntersection` chooses the original facet with that closed facet,
and `buildingFacetClosure_closedFacetIntersection` gives its exact
characterization. Injectivity of the original closed-facet map makes this
choice unique.

`vertexFinset_closedFacetIntersection` identifies the full actual quotient
vertex finset with the intersection of the two input finsets.
`facetPrecedes_closedFacetIntersection_iff` says that this facet is the greatest
common lower facet for the existing incidence relation. Symmetry and the
self-intersection identity follow from the closed-facet characterization.
`closedFacetIntersection_translate` proves compatibility with the original
rational-point action, using the existing action on closed facets and
injectivity of translation on the quotient.

This is a derived internal geometric construction. The proof uses the original
finite actual vertex sets, original closed-facet chart comparison, the affine
intersection theorem and the supplied full Tits comparison. No new external
mathematical assertion is used. The full apartment axioms, including AS5, chart
injectivity and the full Tits comparison remain premises. The file constructs
neither those premises nor a polysimplicial realization, actual root valuation
data or the five witnesses of the host construction theorem. Rank zero is
retained throughout.
