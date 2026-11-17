# Faithful field-point tests in a common target chart

This internal unit works over a complete ultrametric normed field `K`
and a normed extension field `L`, with independent algebra, space,
chart-index and extension-field universes.

On a source atlas containing every full local domain and having a
global chart, a single bounded pullback from a common admissible target
chart determines the complete strong morphism. Equality of that
pullback first identifies the continuous maps, using the actual chart
commutation formula and surjectivity of the source global chart.
Source restriction then identifies the bounded pullbacks from that
fixed target chart on every source chart. The saturated-source
extensionality theorem identifies all other admissible pullbacks.
The target atlas need not have a global chart.

Consequently, if a full field point has an injective evaluation on a
source chart, equality of its images under two strong maps identifies
their complete restrictions to that source chart and any common
admissible target chart. The proof identifies their bounded
pullbacks using `FieldPoint.pullback_eq_of_map_eq` and applies the
existing greatest-chart comparison to the restricted maps. When
the source chart is global, the preceding extensionality argument
identifies the entire original maps.

These results apply to the faithful full point on any small saturated
affinoid spectrum, and to `FaithfulCharacterQuotient.testPoint`.
Those applications retain completeness of `L` and the explicit
`DomainCompletedResidueSurjectivityStatement` premise required to
construct the full field point. Smallness in the independent space
universe is inherited from the spectrum before quotienting.
The kernel-quotient version assumes both complete images lie in the
same specified target chart; it does not require that chart to cover
the target. `commonChartMapEmbedding` packages this result as an
embedding from the family of maps landing in the specified target
chart into the target's actual full field points, by mapping the
quotient test point along each map.

The provenance is internal, from the actual strong-map chart formulas,
restriction compatibility, saturated-source extensionality,
greatest-chart affinoid comparison, and faithful field-point tests.
This unit does not assert that one faithful evaluation identifies maps
to an arbitrary target without the common-chart premise, nor does it
assert full localized pullback preservation.
