# Hausdorffness and the topology of rational points of analytifications

`spaceAnalytificationRationalPoints` proves
`SpaceAnalytificationRationalPointsStatement.{u}` in arbitrary universe `u`.
For an analytification of a separated algebraic space locally of finite type
over a complete ultrametric nontrivially normed field `K`, it gives
Hausdorffness of the underlying analytic space and a topological embedding
of `X(K)` with its étale-chart topology, for every presentation `P₀` of `K`.

## Hausdorffness and injectivity

`IsAnalytification.t2Space_of_isSeparated` identifies the equality relation
on each pair of affine étale tests with the joint ordinary image of their
analytic pullback. Separatedness makes the algebraic pullback a closed
subscheme of the product, so the joint map is closed by the affine
closed-map criterion. Étale chart openness and joint surjectivity then
give Hausdorffness. `IsAnalytification.rationalPoint_injective` uses the
same ordinary analytic pullback point lifting for two `K`-points. A
nonempty pullback of those points has a nonzero quotient of `K` as its
coordinate ring, so the two original points agree.

## The induced topology

`IsAnalytification.continuous_rationalPoint` gives continuity for the
étale-chart topology. For the reverse topology inclusion, fix a rational
open set `W` and a point `y ∈ W`. Separatedness gives quasi-separatedness.
The affine étale chart lifting theorem supplies a finite-type affine
chart and a rational point above `y`. Transport the chart to the spectrum
of its coordinate algebra `A`, take a finite polynomial presentation
`P`, and use Yoneda to obtain the test point `x` of `X`. The affine
coordinate homeomorphism identifies the chart's rational points with
`K`-algebra maps from `A` to `K`. Under this identification, the chart map
on rational points is `RingPoints.changeRing` applied to `x`.

The preimage of `W` in the chart's rational points is open by the
definition of the étale-chart topology. The affine rational-point
embedding makes this preimage the trace of an ordinary analytic open set
`V`. Intersect `V` with the open neighborhood `U` of the chosen rational
lift from `IsAnalytification.etaleChartRationalNeighborhoods`. That
neighborhood comes from the closed image of the off-diagonal part of
the affine chart relation. The analytic chart map sends `V ∩ U` onto
an open set containing `rationalPoint p P₀ y`, by étale openness and
compatibility with change of rings.

If an algebraic rational point has analytic image in this open set,
choose a chart point in `V ∩ U` above it. Membership in `U` makes the
chosen point rational. Compatibility with change of rings and injectivity
identify its image in `X(K)` with the original rational point. Membership
in `V` places that point in `W`. Thus every `y ∈ W` has a neighborhood
for the induced topology contained in `W`. Together with continuity,
this proves the inducing property. The exact-target theorem combines it
with injectivity and Hausdorffness.
