# Actual spectrum diagrams of supplied affinoid atlases

This derived construction uses an already supplied `IndexedAffinoidAtlas` over
a complete ultrametric normed field. The coefficient field, space, and chart
index have independent universes `u`, `v`, and `w`.

The wrapper `ChartObject` orders indices by containment of their actual chart
ranges. Antisymmetry uses the atlas's injectivity of chart ranges; it does not
add an order instance on an arbitrary underlying index type.
`chartAffinoidDiagram` sends an index to the opposite of its actual presented
affinoid algebra and a containment to the opposite of the original bounded
restriction. Its functor laws use the atlas's bounded algebra identities
`restriction_id` and `restriction_comp`. The spectrum diagram is its composite
with the published actual spectrum functor.

`chartRangeDiagram` uses the actual subspace topologies and continuous inclusions.
The spectrum and range objects need not live in the same universe. Both diagrams
are lifted to `TopCat` at `max u v`; `chartSpectrumRangeIso` compares them by the
original embedding homeomorphisms. Its naturality is exactly
`restriction_chart`. The original space is the vertex of `chartRangeCocone`;
its lift is the vertex of `chartSpectrumCocone`. The comparison carries each
spectrum leg to the corresponding lifted range-inclusion leg.

For a monotone chosen atlas morphism, `chartFunctor` is the induced functor on
the range-containment orders. `chartAffinoidMap` retains the actual bounded
pullbacks, and its naturality is the original bounded equation
`restriction_comm`. `chartSpectrumMap` applies the actual spectrum functor,
whereas `chartRangeMap` restricts the given continuous map to the indicated
range subspaces. Their lifted comparison and the spectrum cocones commute by
the original `chart_comm` equations.

The source conventions are Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), Definition 1.2.3 and Remark 1.2.4(i), printed p.16
(PDF p.13), for actual charts and transitive bounded restrictions, and
Definition 1.2.7, printed p.18 (PDF p.15), for chartwise bounded morphisms.
The diagram packaging and explicit universe lifts are derived infrastructure.
This module assumes a supplied atlas and chosen morphism. It constructs no
general analytic gluing, extended atlas, algebra section gluing, localization,
structure sheaf, or analytic site; it makes no colimit assertion.
