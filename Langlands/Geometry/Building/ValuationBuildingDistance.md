# Compatible apartment distances

This internal construction defines a real-valued distance function on the
original `ValuationBuildingData.ReducedBuilding`. It uses the previously
constructed Euclidean metric on the original apartment. The field, group,
quotient, apartment maps and rational-point action are unchanged, at arbitrary
universe `u`. No positive-rank assumption is made.

For `ParahoricBuildingData P`, chart independence uses
`SatisfiesApartmentAxioms`, `HasNormalizerApartmentStabilizer`,
`HasCompatibleApartmentFacets`, and a witness of `IsBuildingTitsSystem` for
the existing zero subgroup. Choosing a common chart for each point pair also
uses a supplied `PolysimplicialRealization R` and
`AbstractBuilding.IsBuilding R.complex R.apartments`. These are the original
building interfaces. No metric on the quotient is assumed.

The first lemma, `IsFacet.subset_apartment_of_mem`, applies compatible facets
after translating the apartment to the base apartment. A facet meeting that
apartment is the image of an affine facet and is therefore wholly contained
in the apartment.

`exists_twoPoint_smul_apartment_eq` chooses facets through two points in one
apartment. The first lemma puts both facets in any other apartment containing
the points. The two-facet Tits transporter stabilizes both facets setwise and
carries one actual apartment onto the other. The previously proved pointwise
facet-stabilizer theorem then shows that it fixes both points.

For `apartment_dist_eq`, suppose a translated chart and the base chart give
coordinates `a,b` and `x,y` for the same two points. Apply that transporter
from the translated apartment to the base apartment. Its product with the
original chart element stabilizes the base apartment and hence belongs to the
actual normalizer by `HasNormalizerApartmentStabilizer`. Equivariance and
apartment-map injectivity identify its action on `a,b` with `x,y`.
The previously proved normalizer isometry gives `dist a b = dist x y`.
The points may lie in distinct facets.

`PairApartmentPresentation x y` records a rational-point group element, two
apartment points, and their equalities with the quotient points `x,y` in
that translated chart. The supplied realization's common-apartment theorem
gives a nonempty presentation type. `pairApartmentPresentation` makes a
classical choice, and `buildingDist R hR x y` is the Euclidean distance
between its two coordinates. Nonnegativity follows immediately. If this
distance is zero, the apartment coordinates are equal, and their recorded
images show `x = y`; this separation implication does not yet require chart
independence.

`pairApartmentPresentation_dist_eq` applies `apartment_dist_eq` to the
relative group element of any two presentations. Consequently
`buildingDist_eq_of_presentation` computes the chosen function in every
presentation. In particular, `buildingDist_translatedApartmentMap` states
that every translated original apartment preserves it, and
`buildingDist_apartmentMap` specializes this to the base chart.

Multiplying a presentation's group element proves `buildingDist_smul`,
invariance under the existing rational-point action. Reversing its two
coordinates proves `buildingDist_comm`. A presentation of a single point in
an apartment proves `buildingDist_self`.

This module is a focused intermediate construction. It proves no triangle
inequality, midpoint NPC inequality, completeness or action continuity.
Those remain consequences to obtain using geometric retractions and the
metric-assembly results. The arguments here are derived from the existing
Library's facet compatibility, actual two-facet transport, pointwise
stabilizers, common apartments and normalizer isometries; no additional
literature assertion is introduced.
