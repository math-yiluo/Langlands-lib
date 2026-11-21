# Product coordinates for a compact open quotient orbit

Let `K` be a compact open subgroup of a second countable locally compact
Hausdorff group `G`, let `H` be a closed subgroup, and let `A` be the open
subgroup of `H` consisting of its elements in `K`. The Haar measures
are regular, and the measure on `H` is also right invariant. Suppose
the homeomorphism from `A × X` to `K` has the form `(a,x) ↦ a s(x)` for
a section `s` into `K`. Assume it sends the product of the restricted
subgroup Haar measure and an s-finite Borel measure on `X` to ambient
Haar restricted to `K`.
`CompactOpenQuotientChartStatement` says that `x ↦ H s(x)` is an open
embedding onto the image of `K` in the left quotient. It transports the
measure on `X` to the restriction of the supplied compatible quotient
measure to that image.

The projection to the quotient is insensitive to the first coordinate.
If two sections give the same coset, their ratio lies in both `H` and `K`,
and uniqueness in the product coordinates gives equality of the second
coordinates. Openness follows from the projection and the chart.
The published `compactOpenOrbitMeasure` at the identity identifies the
restricted quotient measure with the pushforward of restricted ambient
Haar divided by the mass of `A`. In the product coordinates, projection
onto `X` contributes exactly that mass, which is finite and positive.

This internal result packages the quotient normalization for a local
ordinary or twisted Weyl chart using the existing compatible measures.
