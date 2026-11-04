# Strong maps preserve arbitrary affinoid chart changes

Over a complete ultrametric normed field, `mapAffinoidChart` applies a strong
morphism's actual bounded pullback to an arbitrary bounded map from an original
source chart into a presented affinoid algebra. Its spectrum equation is the
composition of the supplied strong map's chart equation with the arbitrary
affinoid test map.

`mapAffinoidChart_isMapChartChange` assumes that the strong morphism's source
atlas has `HasAllLocalDomains`, a property proved for the actual saturation
constructor. Two arbitrary bounded maps into the same presented affinoid
algebra satisfy the full source-atlas `IsMapChartChange` relation, and the entire
image of the first map lies in the second source chart. Each source chart has an
admissible original target chart for the strong morphism. The theorem proves the
full target-atlas chart-change relation for the two bounded composites. The
target atlas is arbitrary, and neither test image need represent a domain.

The proof tests the desired relation on an arbitrary further presented affinoid
algebra, coefficient map, common original target subchart, and bounded
factorization. A finite common-source-chart cover of that test image pulls back
to full domains covering the entire test spectrum. On each domain, the second
pullback leg gives a factorization through a common original source chart. The
input universal source chart-change law supplies the second factorization.
Original strong source restriction equations express the two target composites
using the supplied strong pullbacks on that common source chart.

The strong pullback recovery theorem from `SaturatedStrongChartChange` supplies
the full target chart-change relation on this common source chart. Testing that
relation with the actual pullback-domain algebra identifies the restrictions of
the desired maps. Finite-cover algebra separation proves their complete bounded
map equality and hence the desired universal relation.

This is an internal construction and proof from the imported actual chart
changes, domain pullbacks, strong restriction equations, and algebra separation;
it makes no new external-source attribution. Saturation is required only on the
strong morphism's source. There is no reducedness, nonempty-spectrum,
directedness, greatest-chart, or represented-test-image premise. Strong
composition and analytic sites remain subsequent constructions.
