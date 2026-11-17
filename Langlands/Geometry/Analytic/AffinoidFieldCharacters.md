# Bounded characters and full field points on a global chart

This internal deduction provides two algebraic interfaces for full field-point
pullback arguments. The base field is complete and ultrametric. The field of
values has an independent universe, as do the atlas space and chart indices.

Every field-point evaluation is a bounded algebra homomorphism with constant
one: its norm is the chart seminorm, which is at most the algebra norm. The
bounded evaluation of the actual strong-map image is the original evaluation
composed with the given bounded chart pullback, provided the source atlas
satisfies `HasAllLocalDomains`. Both chosen charts contain the respective
points, and the chosen source chart maps into the chosen target chart.

For the global-chart equivalence, assume that the target `L` is a complete
normed field with its given `NormedAlgebra K L` structure. Also assume the
canonical domain completed-residue surjectivity statement and that one chart
covers the whole space. Equal evaluations in that chart have equal
absolute values and therefore equal spectrum points. Its embedding identifies
the underlying ordinary points. The existing one-chart equality theorem then
identifies the full field points. Conversely a bounded character defines its
spectrum point by pulling back the field norm. The existing character-extension
theorem extends it to every chart, with all restriction compatibilities. These
two arguments give `globalChartCharacterEquiv`. The domain comparison remains
an explicit hypothesis; it is not proved here. Algebraic closedness and an
ultrametric norm on the target field are unnecessary for this equivalence.

For the actual presented affinoid pushout, restriction along its two legs
forms a pullback of bounded-character types in any complete ultrametric target
field. The quotient's coefficient relation gives commutation. The established
bounded pushout uniqueness gives joint injectivity, and its lift theorem gives
a preimage of every compatible character pair. This result retains an
independent target-field universe and imposes no smallness assumption on its
carrier. It concerns characters of the actual affine algebras; the full
localized geometric pullback-preservation target is a separate obligation.

The provenance is internal: these are deductions from the published field-point
norm/compatibility axioms, the conditional all-chart extension theorem, and the
actual affinoid pushout's universal property. No external source is transcribed.
