# Pointwise fixers of integer-building facets and their closures

This internal prerequisite concerns the original reduced quotient attached to
supplied `IntegerValuationBuildingData` over an arbitrary field with an
integer-valued valuation. Its statement is
`Langlands.Geometry.Building.IntegerBuildingFacetFixersStatement`.
There is no characteristic, local compactness, affine-root-system, model
existence, or parabolic-correspondence premise.

For any set of real affine functionals on an affine torsor,
`midpoint_mem_facet_of_mem_facetClosure` proves that the midpoint of a point
and a point in its formal closed facet lies in the original open sign facet.
At a root positive or negative at the first point, the second value has the
corresponding weak sign, so their average has the original strict sign.
At a root vanishing at the first point, both values vanish.
This extracts the sign calculation already used in the published
`AffineRootSystem.IsVertex.eq_of_mem_facetClosure` proof in
`GenericVertexApartmentRigidity`, without using its vertex hypothesis.
The derived `affineMap_eq_self_of_facet_fixed` applies preservation of
midpoints and reflection about the midpoint: an affine map fixing the first
point and the midpoint also fixes the second point.

For the original integer-building quotient,
`smul_apartmentMap_eq_of_facet_fixed` uses the published
`exists_normalizer_eq_on_translated_facetClosure`. An element fixing the
open facet agrees with an actual normalizer element on the whole formal
closure. The published `apartmentMap_injective` shows that this normalizer
element fixes the open facet in apartment coordinates. Its affine action
then fixes the formal closure by the midpoint lemma, so the original group
element fixes its image in the quotient.

`pointwiseFixer_buildingFacetClosure` conjugates this argument into any
translated apartment and applies the published
`buildingFacetClosure_eq_image`. Thus a full building facet and its original
combinatorial closure have equal pointwise fixer subgroups in the same
rational-point group. The reverse containment uses the published inclusion
of a facet in its closure.

Finally `pointwiseFixer_le_of_facetPrecedes` uses the original common-apartment
incidence relation: a lower incident facet is contained in the closure of
the upper one, and hence the upper facet's pointwise fixer fixes the lower
one. The named proposition and its theorem combine exactly this reversal
and the closure-fixer equality. These are internal consequences of the
published quotient, normalizer, facet-incidence and affine-action APIs.
They construct neither integral models nor a facet-parabolic bijection,
and they do not prove the host split-torus existence theorem.
