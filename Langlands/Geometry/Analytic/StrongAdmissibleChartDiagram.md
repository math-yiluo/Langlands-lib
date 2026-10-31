# Full strong maps on all admissible chart pairs

This derived construction works with actual indexed affinoid atlases over a
complete normed ultrametric field. It retains independent coefficient, ambient
space and original chart-index universes. The chart algebras are genuine
`PresentedAffinoidAlgebra` objects and every morphism retains bounded algebra
maps. No reducedness assumption is imposed.

The original convention is Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), Definition 1.2.3 and Remark 1.2.4(i), printed p.16 /
PDF p.13, and Definition 1.2.7 and the composition construction after Proposition
1.2.8, printed p.18 / PDF p.15. Registered source:
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The source assigns compatible affinoid morphisms to every admissible pair of
charts. The diagram packaging and the directed composition comparison here
are derived infrastructure for that convention, not separately numbered source
assertions. General composition in the source uses extension and finite-cover
gluing, which this unit does not construct.

`chartStrongDiagram` sends each original chart, ordered by actual domain
containment, to its original chart-domain presentation. It retains every
original chart contained in that domain. Its arrows are the published full
strong chart inclusions. Their proved identity and composition equations
give the functor laws. Forgetting the strong-map data gives exactly the
published diagram of actual range subspaces.

For any full strong map `f`, `AdmissibleChartPair` is the subtype of pairs of
original chart objects whose source image lies in the target chart. The
coordinatewise containment order gives its category. `chartPairSource` and
`chartPairTarget` are its two projection functors. No target selection, monotone
choice or directedness hypothesis is needed.

`chartRestrictionTransformation` has the published full strong restriction
`f.onCharts i j h` at each admissible pair. Naturality first enlarges the
source, then the target, using the two existing full strong naturality
equations. Every equality concerns all admissible bounded pullbacks in the
actual chart-domain presentations.

`chartPairAffinoidTransformation` packages the same original bounded maps
in the opposite category of actual presented affinoid algebras. Its naturality
is exactly `f.restriction_comm`. Applying the actual spectrum functor defines
`chartPairSpectrumTransformation`. `chartPairRangeTransformation` restricts
the original continuous map on each admissible pair of range subspaces.
Forgetting `chartRestrictionTransformation` gives that range transformation
definitionally. `chartPairSpectrumRange_naturality` intertwines the actual
spectrum maps and range maps through the published lifted chart
homeomorphisms; the proof is the original chart-square equation after forgetting
the lift and subtype.

`onCharts_compOfDirected` compares the restriction of the published directed
ambient strong composite with the actual categorical composite of two local
strong restrictions along any admissible original chain `i,j,k`. It assumes
directed original intermediate and target atlases, with no directed source
condition and no greatest ambient chart. Greatest-target detection on the
actual final chart domain reduces equality to bounded maps. The ambient
directed composition formula and the local greatest-chart composition formula
give the same bounded composite for every contained source chart.
`onCharts_comp_independent` compares two admissible intermediate choices
through their equality with this same full ambient restriction.

`ext_of_onCharts` detects equality of global strong maps from one common
admissible target chart and equality of the two full local restrictions for
each original source chart. The target atlas is directed. Chart coverage
first derives equality of the original continuous maps. Evaluating equality
of local strong maps at their outer source and target charts gives equality
of the corresponding bounded algebra maps. The published directed
extensionality theorem then recovers every admissible pullback. Equality on
spectrum points alone is not used to identify algebra maps.

These are diagram, composition and equality constructions for supplied actual
atlases. Extended atlases, general finite-cover gluing, unrestricted strong
composition and localization, structure sheaves, étale sites and Harris tower
constructions remain separate obligations.
