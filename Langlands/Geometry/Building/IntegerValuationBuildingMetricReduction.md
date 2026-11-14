# Complete NPC metrics from retractions on integer-valued buildings

This module contains the generic apartment-metric, gluing and completeness
construction formerly in `UnramifiedBuildingMetricReduction`. It retains every
public Lean declaration name, statement and proof from that part of the published
module. The original module imports this one, so existing consumers keep the same
interface. The purpose of the separation is to make the construction available
without importing maximal-unramified descent or special-torus statement modules.
This is an internal extraction of already published mathematics, with no new
source assertion or strengthening of its hypotheses.

The field `k : Type u` is arbitrary, with an integer-valued valuation `v` and an
affine group scheme `G`. All conclusions concern the existing supplied
`B : IntegerValuationBuildingData v G`, its original apartment, quotient and
rational-point action. The datum still supplies full V6; the module asserts no
existence of such data or of retractions.

`KPApartmentData.rootDistance` is the square root of the finite-support sum of
squared evaluations of the actual relative roots on an apartment displacement.
For integer-valued building data, `rootDistanceFintype` supplies the finite-root
instance. The local root norm, `rootMetricSpace` and `rootNormedAddTorsor` use the
existing canonical root-coordinate norm. `rootDistance_eq_dist` identifies the
explicit formula with that apartment metric. `root_nonpositivelyCurved` transports
the inner-product midpoint inequality across an affine torsor isometry, and
`root_properSpace` uses finite dimensionality.

`exists_normalizer_smul_eq_of_smul_apartmentMap_eq` applies the original quotient
relation to compare a translated apartment point in the original apartment with
a normalizer translate. `exists_rootDistance_normalizer_smul_lt_imp_eq` proves
discreteness of normalizer orbits: the affine roots form a locally finite
reflection arrangement by the existing integer-valued full-V6 results, and the
normalizer affine action permutes that arrangement. The generic arrangement
orbit-discreteness theorem supplies a radius fixing the given apartment point.

The gluing construction assumes common apartments and a function `d` invariant
under the existing rational-point action, with the prescribed apartment root
distance and point-centred contracting apartment retractions. Each translated
apartment is an isometric chart. The retraction onto a translated apartment is
the given retraction conjugated by that rational-point translate.
`isRetractionGluedDistance` verifies the existing generic gluing interface, which
provides a metric with distance exactly `d` and nonpositive curvature.

For completeness, `smul_apartmentMap_eq_of_dist_lt` places an apartment point and
a sufficiently close rational translate in a common apartment. The quotient
relation reduces their displacement to the normalizer, whose discrete orbit
forces equality. `exists_forall_dist_smul_lt_imp_eq` conjugates this conclusion to
all building points. `completeSpace_of_isometry_apartmentMap` then uses translates
of the compact image of a closed apartment ball and the generic discrete-orbit
completeness theorem.

`exists_metric_of_retractionDistance` assembles the resulting metric, its exact
equality of distances with `d`, completeness, nonpositive curvature and isometry
of the original rational-point action. No downstream metric-existence proposition,
coefficient action, special torus, stable apartment or fixed point is used or
constructed here. The retractions remain an explicit premise.

The mathematical provenance is unchanged from the published construction:
Kaletha–Prasad Section 4.2 is implemented through the existing root metric,
retraction gluing, affine-arrangement discreteness and discrete-orbit completeness
results. The original module's paired explanation retains its source locations
and the maximal-unramified applications. This extraction changes only the import
boundary and file location of the generic declarations.
