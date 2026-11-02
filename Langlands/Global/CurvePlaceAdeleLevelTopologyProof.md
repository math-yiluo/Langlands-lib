# Proof of the topology of actual discrete curve-place adelic levels

Author: Worker 208.

`curvePlaceAdeleLevelTopology` proves exactly
`CurvePlaceAdeleLevelTopologyStatement` in arbitrary common universe `u`.
It adapts Worker 208's finite-adele level topology proof to the concrete
curve-place restricted product and its actual completion factors.

Restricted-product coordinate evaluations prove continuity of the
canonical coordinate ring equivalence. For its inverse, the assembled
coordinates first define a map to the principal-filter restricted product
imposing integrality outside `S`. This has the coordinate-induced topology,
so coordinate projections prove continuity. The continuous inclusion into
the cofinite restricted product proves continuity into the ambient ring,
and corestriction proves continuity into the level subspace. The existing
inverse identities now give the homeomorphism for the original map and
topologies.

The transition inclusion becomes the open inclusion of the smaller level
into the ambient ring after composition with the larger level's open
inclusion, so it is an open embedding. Every restricted-product element
has only finitely many nonintegral coordinates by its membership condition;
that finite set supplies a containing level. These open levels cover the
ring, so continuity on each level implies continuity at each point. The
converse is restriction of continuity.

The statement's Markdown records the derived Conrad provenance and the
retained global-function-field, finite-pole, presentation and geometric
obligations. This proof assumes no finite-pole theorem for elements of `F`.
