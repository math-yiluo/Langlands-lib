# Rationally surjective products of split unipotent subgroups

`Langlands.GroupScheme.RelativeRoot.FiniteFieldSplitUnipotentProductStatement.{u}`
is a proposition target at arbitrary universe `u`. It concerns actual group
schemes over every finite field `k : Type u` and the actual scheme morphism
`subgroupMultiplication j c` from `V × C` to `U`, sending `(v,z)` to `j(v)c(z)`.

The three groups are smooth, affine, connected, and split unipotent in the
existing finite Ga-series sense. The two maps are closed subgroup embeddings.
Their intersection is the existing scheme-theoretic categorical pullback
`subgroupIntersection j c`; it is additionally required to be smooth, connected
and split unipotent. Its affineness follows from closedness of the embeddings.
The remaining hypothesis says exactly that multiplication covers every
`k`-rational point of `U`, without passing to a field extension.

The conclusion is that the original multiplication morphism is smooth and
surjective on underlying scheme points. This does not assert that every point
on every test scheme lifts without a cover. Smooth surjectivity provides the
usual local lifting interface, which can be used for descent of all-test closed
subgroup containment.

The provenance is internal and derived. This target isolates the geometric step
in a finite-field transporter argument. Counting each rational multiplication
fiber by the rational points of the intersection, then applying the existing
finite Ga-series point counts, gives
`dim V + dim C = dim U + dim(V ∩ C)`. Smoothness of the intersection ensures that
it also computes the differential kernel. One possible proof uses the action
of `V × C` on `U` by left multiplication and inverse right multiplication:
Kostant–Rosenlicht gives a closed orbit, while the dimension equality forces it
to fill connected `U`; its smooth stabilizer gives smoothness of the orbit map.
The relevant published interfaces include `subgroupIntersection`,
`Rational.SplitSeriesPointCount`, `SchemeAction.quotientOfClosedAffineOrbit`, and
`unipotentAffineOrbitClosed`. The counting helper
`Rational.SplitUnipotentProductPointCount` supplies the dimension equality when
available. These observations explain the target's origin; this module contains
no proof of the geometric assertion.
