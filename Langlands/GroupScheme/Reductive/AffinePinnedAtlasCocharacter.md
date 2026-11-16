# The invariant positive-coroot cocharacter on a pinned atlas

For an affine pinned atlas of a group scheme over an arbitrary scheme, this
internal construction assembles the charts' canonical positive-coroot
cocharacters into an actual cocharacter of the original group pulled back to
the atlas. A supplied natural `RelativePinnedComparison` makes this
cocharacter compatible with the corrected descent datum.

`AffinePinnedChart.cocharacter` transports the chart model's canonical
cocharacter through its isomorphism with the original group pullback.
`cocharacter_pull` identifies its normalized direct pullback with the previously
defined chart cocharacter in the original group.

`AffinePinnedAtlas.cocharacter` uses arbitrary disjoint-component homomorphism
assembly. On each component it first identifies the pullback of the
multiplicative group with the component's multiplicative group, applies the
chart cocharacter, and then inverts the comparison from the iterated to the
direct original-group pullback. Component restriction recovers the chart
cocharacter. Pullback tower coherence then evaluates the assembled cocharacter
at any actual chart coordinate.

`cocharacter_ext_on_charts` detects equality of cocharacters on pairs of chart
coordinates. The proof restricts successively to the inverse images of the
two atlas components. Full faithfulness of restriction to arbitrary disjoint
components and the multiplicative-group pullback isomorphisms detect equality;
cocharacter tower coherence identifies these successive restrictions with the
normalized direct restriction. No finiteness or connectedness is assumed.

`transition_cocharacter` applies this criterion to the two direct atlas
cocharacters and their corrected transition. Normalized restriction conjugates
the transition by the endpoint comparison
(`Dynamic.pullbackCocharacter_comp_pullIso`). The chart evaluation of the
assembled transition, the two chart evaluations of the cocharacters, and
`AffinePinnedChart.transition_cocharacter` give the local equality.
Cancellation of the target endpoint comparison yields
`actualTransition_cocharacter` for the actual atlas group pullbacks.
Specializing to the double-overlap projections gives `overlap_cocharacter`,
the exact compatibility equation with the constructed descent overlap.

The provenance is internal disjoint-component assembly, actual pullback
coherence, and the already proved preservation of chart cocharacters by a
supplied comparison operation. This module establishes neither existence of
that operation nor effectivity of the datum or descent of the cocharacter,
and it does not prove the unconditional quasi-split inner-form theorem.
