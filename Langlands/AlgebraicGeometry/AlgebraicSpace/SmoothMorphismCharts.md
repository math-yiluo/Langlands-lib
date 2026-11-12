# Common étale chart squares and smooth morphisms

Authors: Worker 131 and Worker 156. The common-chart argument is adapted from
Worker 156's independently submitted `FlatMorphismCharts` development, with
the chart geometry factored into reusable constructions and the property
specialized here to smoothness.

`EtaleMorphismChart f` packages a commuting square from a scheme morphism to
`f`, with étale source and target charts. It does not require either chart to
be surjective. Two such squares have represented common source and target
schemes, formed by pulling back their charts. `comparison` is the induced
map between these schemes, constructed using the target pullback and fullness
of scheme Yoneda. Its two projection identities come from that pullback.

`property_of_chart` isolates the resulting scheme argument. It retains four
explicit hypotheses on a scheme property: composition with an étale map on
each side, cancellation of an étale second map, and descent through a
surjective étale source map. If the first chart has surjective source and its
scheme map has the property, every other chart's scheme map does too. The
common-source projection to that other chart is étale and surjective; both
common-target projections are étale. The two projection identities therefore
allow successive composition, cancellation, composition and source descent.

For smoothness the composition hypotheses are standard scheme instances.
Cancellation uses the smoothness of an étale morphism's diagonal and Mathlib's
diagonal criterion. Source descent uses the published
`smoothEtaleSourceDescent` theorem. Thus `IsSmoothMorphism.smooth_chart` tests
the existing existential smooth-morphism definition on any commuting étale
chart square. If its source chart is also surjective, the scheme smoothness
condition is equivalent to that definition, as stated by
`isSmoothMorphism_iff_smooth_chart`.

This is an internal construction and a derived chart-independence argument,
using existing Library scheme smoothness results. No new literature assertion
or descent along limits is asserted here.
