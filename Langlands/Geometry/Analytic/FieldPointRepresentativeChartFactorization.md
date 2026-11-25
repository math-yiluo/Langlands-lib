# Faithful representatives over prescribed small chart spectra

This internal construction works over a complete ultrametric normed
field `K` with a complete normed extension field `L`. The algebra,
space and extension-field universes are independent. Presentations
are saturated, with their space and chart-index universes both equal
to the space universe, as in `LocalizedEtaleFieldPointPullbackStatement`.

Each actual chart spectrum is small in its presentation's space
universe, since its chart map is injective into that space.
`A.smallChartSpectrum i` is the saturated small spectrum of the
actual chart algebra. The identity map of that algebra supplies
`A.smallChartSpectrumInclusion i`, an actual complete strong map
into `A` whose entire image lies in the selected chart.
These constructions do not require a choice of extension field.

For a full field point `p` lying in that chart, `p.smallChartPoint`
is the full point on the small chart spectrum determined by its
actual bounded evaluation. The small chart inclusion maps this full
point to `p`. This identity retains the explicit domain
completed-residue comparison and uses the existing exact image
formula for canonical maps from small spectra into target charts.

Suppose a strong map `f : P → A` carries a containing chart `k`
of a full point `p` into a prescribed target chart `i`.
`p.chartTestPullback` is the actual bounded pullback from chart `i`
to chart `k`, followed by the quotient by the actual kernel of
`p`'s evaluation at `k`. Composing with the faithful descended
character gives exactly the evaluation at `i` of the full image
point `p.map f`. This bounded-map identity does not require
completeness of `L`.

The contravariant small-spectrum map of this bounded pullback
defines `p.chartTestToSmallChart`, directly from the faithful
representative at `k` to the small spectrum of chart `i`.
Under the domain completed-residue comparison it maps the entire
faithful full test point to the small chart point of the full image
evaluation. The proof applies full-point naturality of the actual
small-spectrum map and the preceding exact character identity.

Composing this direct map with the small chart inclusion equals
the representative map at `k` followed by `f`, as complete strong
morphisms. Both composites land in chart `i`; their full test-point
images agree by full-point functoriality and the exact image
identities. Faithful detection in this common chart proves the
triangle. The implemented proof retains the domain completed-residue
comparison.

For two strong maps out of `P`, prescribe a containing chart of each
image of `p`. Saturation supplies a containing source chart
admissible to each image chart. The atlas net axiom refines the two
source charts to one containing chart admissible to both targets.
`exists_chartTest_pair_factorization` gives both direct maps,
their full test-point image identities, and both complete strong
triangles from that one faithful source.

The provenance is internal, from actual chart pullbacks,
character-kernel quotients, canonical small-spectrum maps,
full-field-point functoriality, and the atlas net axiom. This module
does not assert the final unconditional localized pullback
preservation theorem.
