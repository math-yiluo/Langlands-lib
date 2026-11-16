# Assembled transitions for an arbitrary pinned affine atlas

This internal construction assumes an affine pinned atlas of an actual group
scheme and a supplied `RelativePinnedComparison`. It assembles actual
automorphisms of the original group pulled back to arbitrary test schemes.
No finiteness hypothesis is imposed on the point-indexed atlas.

For one fixed chart and a map to the atlas, `chartToAtlas` decomposes the test
scheme into inverse images of the atlas components and assembles the actual
chart transitions there. `transition` performs a second such assembly for a
pair of arbitrary atlas-valued maps. The actual coproduct inclusion equations
give the required base-map equalities at every step.

The evaluation lemmas factor any specified chart coordinate through its
inverse-image component. Evaluation of the assembled isomorphism on this
factorization and the published chart-transition pullback law identify it
with the prescribed chart transition.

`iso_ext_on_charts` reduces equality of actual isomorphisms to their values
on every pair of chart coordinates by the two nested inverse-image
decompositions. The three-coordinate version uses one further decomposition.
`transition_self` follows by evaluating the same chart coordinate at both
ends. `transition_pull` evaluates both sides on pairs of chart coordinates
and uses successive-pullback coherence. `transition_trans` evaluates on
triples of coordinates; the chart-transition cocycle gives precisely the
composition of the two assembled transitions. These laws hold on every
common test scheme and along every further scheme map.

The provenance is internal composition of actual chart transitions and
disjoint-component assembly. The correction operation remains an explicit
input; no existence of it or descended object is asserted here. The
isomorphisms constructed here are automorphisms of the direct pullback of
the original group; expressing them as an actual atlas Čech datum requires
the direct/iterated pullback comparisons.
