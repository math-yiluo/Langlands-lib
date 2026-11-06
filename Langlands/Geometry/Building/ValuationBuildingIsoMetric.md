# Metric witnesses on the actual transported valuation quotient

This internal construction takes supplied valuation-building data `B`, an
actual ambient group-scheme isomorphism `f : G ≅ H` over the same
nonarchimedean local field, and a supplied `B.MetricRealization`. All objects
remain in the common universe `u`.

`MetricRealization.mapIsoMetric` induces the target metric along the inverse
of `B.mapIsoReducedBuildingEquiv f`. `mapIsoIsometry` bundles that exact inverse
as an isometry equivalence. Completeness follows from this isometry, and the
nonpositive-curvature midpoint inequality transfers by transporting its original
midpoint.

Inverse equivariance uses the actual inverse rational-point map of `f`. The
existing target action is therefore isometric for the induced metric.
Continuity of each orbit is the composition of the inverse rational-point map,
the original continuous orbit, and the forward quotient isometry. Both
rational-point groups carry their canonical identity-test point topologies.

`MetricRealization.mapIso` packages these witnesses on the same transported
valuation quotient used for the full fixer and compact-stabilizer images.
Its metric field is exactly `mapIsoMetric`.

The provenance is internal metric transport and the published actual quotient
equivariance and affine-scheme point-map continuity. No new literature assertion
is made. The construction assumes its original building data and metric
realization; it supplies neither their existence nor a special point or an
integral-model comparison.
