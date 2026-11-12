# Source restrictions over fixed target dimensions

Author: Worker 109. This is derived supporting geometry for the adelic
openness proof, building on the actual target point opens in
`SmoothDimensionOpenSubspaces` and the all-chart dimension law in
`SmoothRelativePointDimension`.

The source subfunctor is the preimage of a target stratum. Its inclusion
is a representable open immersion by the actual subfunctor pullback square.
`sourceSpace`, `sourceInclusion` and `restrictedMap` construct the actual
source space and restricted arrow. The square is a pullback of presheaves,
and the source inclusion has exactly the inverse-image point locus.
The same finite dimension index therefore covers all source points.

A commuting etale chart of the restricted map gives a chart of the original
map by composition with the open inclusions, on the same source and target
schemes. Its source points lie in the specified dimension locus, so the
all-chart numerical law identifies its actual local fibre dimension with
the chosen natural number.

The helper `smoothOfRelativeDimension_of_localDimension` proves that a
smooth map with locally Noetherian source and constant actual local fibre
dimension is smooth of that relative dimension in the standard-smooth
chart sense. On each actual source component the existing connected-source
theorem supplies a smooth dimension. The pure-fibre theorem compares it
with the assumed local dimension at a point of that nonempty component.
Equality of the natural dimensions and Zariski locality at the source
finish the proof, including an empty source without a special case.
Applying this result proves fixed smooth relative dimension on every
locally Noetherian source chart of a stratum restriction.

Finite-presentation compact atlases for the restrictions, connected-fibre
and other model properties, uniform Lang-Weil and adelic assembly remain
subsequent obligations.
