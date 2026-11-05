# Intersection lifts and uniqueness for the affine-chart Weil restriction

This is derived construction infrastructure for Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), Example 4.2,
printed pp.9–10. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
Conrad invokes restriction of scalars along finite locally free ring maps and
its construction from affine opens. The explicit intersection lifts and
cover argument here are derived from that construction, rather than quoted
as a separate result of the paper.

Fix an arbitrary common universe `u`, commutative rings `A` and `B`, an
`A`-algebra structure on `B`, and `Module.Finite A B` and
`Module.Projective A B`. Let `Y` be an actual scheme over `Spec B`, expressed
as an object of `Over (Spec B)`, with `LocallyOfFiniteType Y.hom`.
Write `G` for the actual `affineChartWeilRestriction A B Y`, constructed by
gluing the existing affine restrictions of all affine opens of `Y`.
Its already constructed counit defines the canonical comparison

`Hom_A(T,G) → Hom_B(T ×_(Spec A) Spec B,Y)`

on every actual test scheme `T` over `Spec A`. No affineness or finiteness
condition is imposed on the test scheme.

The principal construction is
`affineChartWeilRestrictionIntersectionLift`. Given affine opens `U,V` of
`Y` whose intersection is affine and two actual maps
`p : T → Res(U)`, `q : T → Res(V)` whose canonical comparisons agree after
inclusion into `Y`, it constructs a map
`r : T → Res(U ∩ V)`. Its composites with the existing affine
Weil-restriction maps for the two open inclusions are exactly `p` and `q`.
These identities concern the specified coordinate maps, without replacing
them by maps chosen up to isomorphism.

First, `relativeOpenIntersection_isPullback` identifies the actual relative
open-intersection square, whose inclusions are the published
`openOverHomOfLE` maps, as a pullback by forgetting to the standard
intersection square of schemes. `relativeOpenIntersectionLift` is its
universal lift, with both projection identities. These initial constructions
work over any commutative ring `R`, with no finite-type or affineness
assumption on the ambient scheme.

`affineWeilRestrictionTestEquiv` packages the previously proved injectivity
and surjectivity of the affine canonical comparison into a Hom-set
equivalence on arbitrary test schemes. The principal intersection lift
applies its inverse to the relative open-intersection lift of the two
comparisons. Its two projection identities follow from affine comparison
injectivity, compatibility with the existing affine restriction maps, and
the two relative intersection projection identities.

`affineChartWeilRestriction_chart_eq` then proves that these two compatible
chart maps have equal composites into `G`. Both factor through the actual
intersection chart, and naturality of the chart inclusions identifies those
composites. The hypothesis that this intersection is affine is explicit.
It is not asserted for arbitrary nonseparated schemes.

`affineChartWeilRestrictionTestCover` pulls the genuine chart open cover of
`G` back along any actual map `p : T → G`.
`TestChart`, `TestChartι` and `TestChartMap` equip its components with
their structure maps to `Spec A`, their actual cover morphisms to `T`,
and their actual maps into the corresponding affine restriction charts.
`TestChartMap_fac` proves that a component's map to its chart, followed
by that chart's inclusion in `G`, is its cover map followed by `p`.
The construction uses the actual scheme pullback projections.

`affineChartWeilRestrictionComparison_injective_of_affineIntersections`
proves injectivity of the global comparison under the explicit hypothesis
that every pair of affine opens of `Y` has affine intersection. For two
maps with equal comparisons, first pull the chart cover back along the
first map. On each component, pull it back again along the second map.
On the resulting components both morphisms factor through affine charts.
Naturality and exact chart compatibility of the comparison give agreement
of the local comparisons in `Y`; the intersection construction therefore
gives equality in `G`. Two applications of the open-cover equality
criterion give equality of the original scheme morphisms, and hence of
their morphisms over `Spec A`.

`affineChartWeilRestrictionComparison_injective` specializes this result
to the source-relevant hypothesis `IsSeparated Y.hom`. Since `Spec B` is
affine and therefore separated, `Y` is absolutely separated. Its diagonal
is affine, so Mathlib's `IsAffineOpen.inf` proves the required affine
intersection property. The result still quantifies over every test scheme.

This unit constructs the intersection and test-chart maps and proves their
intrinsic laws, including uniqueness for the actual global comparison.
It does not establish surjectivity of that comparison. The finite-fiber
affine-neighborhood and inverse-gluing arguments for full nonaffine
representability, the quasi-projective instantiation and preservation
claims, and the local and adelic topology comparisons remain obligations
of the larger development. There are no field, separability or topological
hypotheses in this construction.
