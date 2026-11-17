# Recognition and finiteness of actual affinoid inverse images

This internal construction works with independent field, space, and original
atlas index universes. For a strong map between saturated presentations, a
recognized target subset contained in a chosen target chart, and an admissible
source chart, `recognizedPullback` constructs a recognized source subset whose
literal locus is the intersection of that source chart with the inverse image
of the target locus.

The construction takes the actual full-domain affinoid pushout, regards it as
a local domain of the saturated source atlas, and uses closure under all local
domains to choose an existing source chart. Original-chart recognition gives
the required recognized subset. The strong-map chart equation proves its exact
locus and admissibility.

For any recognized subset having this inverse-image locus, the earlier bounded
pushout comparison identifies its complete bounded pullback with the original
second pushout leg followed by a bounded algebra equivalence. The latter is
finite Banach because its bounded inverse supplies controlled lifts with the
single generator `1`, using the published lemma from `QuasiIsoSourceEtale`.
Assuming that the original bounded chart map `g.pullback i j hij` is finite
Banach and assuming `FiniteBanachPushoutStatement K`, this proves finiteness
of every such recognized pullback. If both chosen charts have global range,
these same two finiteness premises prove that the strong map is finite over
the entire target in the full-recognition sense.

These are derived consequences of full-domain base change, saturated atlas
closure, and the bounded comparison in `RecognizedContainedMap`. The finite
Banach pushout statement remains an explicit premise. This module does not
prove unrestricted pointwise lifting in the analytic étale site.
