# Original global quotient point coordinates on each cover component

This internal Task 7200 adapter compares actual original group point lifting
through a tower with the prescribed direct group pullback comparison. It uses
the original underlying morphism retained by the lift and the actual pullback
projection equations.

It applies exact component point-chart recovery to the constructed finite face
cover. `quotientComponentPoint` maps an original global quotient point to the
original vector quotient of one actual chart, using the actual global
component isomorphism. `globalFaceQuotientCharts_component` identifies its
canonical free-module point sections with the original lifted quotient module
chart through the prescribed actual module composition and piece
isomorphisms, on every test.

The provenance is derived from actual group pullback projection coherence,
exact assembled point-chart component recovery and the original module and
quotient component maps. The scalar compatibility between two original chart
components remains a consumer obligation.
