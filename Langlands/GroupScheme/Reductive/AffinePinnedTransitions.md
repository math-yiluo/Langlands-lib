# Actual transitions between affine pinned charts

This internal construction starts with the affine pinned charts of an actual
group scheme. The original base and every common test scheme may be arbitrary;
there are no connectedness, affineness, finiteness or nonemptiness assumptions
on these schemes.

`Descent.pullbackComparison_comp` compares two ways of removing successive
actual pullbacks. Its proof uses the universal property of the scheme pullback:
both composites have the same projection to the original group and the same
projection to the base. The base-change comparison is also natural in group
homomorphisms. These two facts prove `AffinePinnedChart.identify_pull`.

For a chart `C`, a map `f` from a common test scheme to its model base, and a
specified base map `k` with `f ≫ C.map = k`, `identify` is the actual isomorphism
from `k*G` to `f*C.model.group`. It first uses the inverse direct/iterated
pullback comparison and then pulls back the chart's given isomorphism.
`comparison` from chart `C` to chart `D` is the inverse identification for `C`
followed by the identification for `D`. Cancelling the middle identification
proves identity and composition; `identify_pull` proves further pullback
compatibility.

The remaining constructions take a supplied `RelativePinnedComparison`.
`correctedComparison` applies its correction operation to this actual chart
comparison. Its identity, composition and pullback laws follow from those of
the original comparisons and the supplied operation. `transition` conjugates
the corrected comparison by the chart identifications, so it is an actual
automorphism of `k*G`. Cancellation of the intermediate chart identification
proves the cocycle equation `transition_trans`. The supplied naturality law
and `identify_pull` prove `transition_pull` along every further scheme map.

`torusInOriginal` and `cocharacterInOriginal` express the chart's normalized
coordinate torus inclusion and positive-coroot cocharacter in `k*G` using the
inverse identification. The supplied torus and cocharacter clauses, followed
by cancellation, prove that each transition carries these actual inclusions
and cocharacters to the corresponding ones for the other chart. The torus
claim includes an actual isomorphism of the two coordinate tori and its exact
inclusion square.

The provenance is internal: the definitions compose the actual chart data,
the published pullback comparisons, and a supplied correction operation. The
module constructs these local transitions and proves their laws. It does not
prove existence of the supplied correction operation, assemble a global
overlap isomorphism, descend objects, or prove quasi-split inner-form existence.
