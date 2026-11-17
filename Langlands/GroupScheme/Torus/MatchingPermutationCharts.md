# Gluing comparisons between matching permutation charts

This internal derived module compares two actual systems of split charts over a
small étale covering family. The finite coordinate type may vary with the cover
member. `SameLocalPermutations` means that, near every point of every actual
overlap, both systems satisfy the same coordinate permutation on all relative
tests. The overlap neighbourhood and permutation are shared by the two systems.

`comparisonPoint` expresses the actual chart comparison on an original-group
point using the chart point equivalences. `coordinates_pullbackPoint` identifies
these coordinates with the pulled-back point. `comparisonPoint_projection` and
its specified-lift version show that the comparison point is the projection of
the actual local group isomorphism applied to that pullback point.

`comparisonPoint_eq_of_agreeBy` proves equality of the comparisons wherever the
two systems obey the same supplied permutation: evaluate both outputs in one
chart, use the common permutation to switch charts, and cancel the coordinate
point equivalence. This compares all tests, not only geometric points.

For arbitrary equal-source-projection tests over two cover members, form their
actual map to the chart overlap. Pull a chosen overlap open back to the test
scheme and lift it to that open. The preceding comparison identity proves local
equality of the projected outputs. The scheme local equality theorem gives
global equality. Thus the actual chart-comparison homomorphisms satisfy the
all-test compatibility needed by `EtaleCoverHomDescent`.

The argument is symmetric in the chart systems, so it also proves compatibility
of the inverse comparisons. `matchingChartsIso` glues the local comparisons and
their inverses to an actual global group-scheme isomorphism.
`baseChange_matchingChartsIso` records exact recovery of every original local
comparison. No affineness hypothesis on the base or either group scheme is
imposed; the universe is arbitrary and empty finite coordinate types are allowed.

The provenance is internal and derived: this combines the normalized all-test
chart definitions, scheme local equality, and actual étale-cover homomorphism
descent. It adds no literature claim beyond those imported constructions.
