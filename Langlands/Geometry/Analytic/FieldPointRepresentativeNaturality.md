# Naturality of faithful local field-point representatives

This internal construction works over a complete ultrametric normed
field `K` with a complete normed extension field `L`. The algebra,
space and extension-field universes are independent. Source and
target are saturated presentations whose space and chart-index
universes are both the space universe, as in
`LocalizedEtaleFieldPointPullbackStatement`.

The faithful local representative of a full field point has a global
chart on its source, so every point of that source maps into the
selected actual target chart. `chartTestMap_mem` records this fact
without an extra completeness requirement on `L`.

Suppose a strong map `f` carries an actual source chart `i` into a
target chart `j`, and the full field point `p` lies in `i`. Its actual
bounded chart pullback identifies the evaluation at `j` of the full
image point with the source evaluation precomposed with that
pullback. Descending this bounded map through the kernels of these
two actual evaluations defines `p.chartTestTransition`. The resulting
map runs from the faithful representative at `i` of `p` to the
faithful representative at `j` of its full image. Each chart's
spectrum is small because its chart map is injective into its
presentation's space.

Under the explicit domain completed-residue comparison,
`chartTestPoint_transition` identifies the entire mapped faithful
test point with the faithful test point of the image evaluation.
It applies the existing full-point naturality of the actual
descended quotient map, preserving every chart evaluation.

The representative square commutes as an equality of complete
strong morphisms. Both composites have image inside the same
target chart `j`. On the faithful source test point, functoriality
of full-point pushforward and the representative-image identities
give the same full field point. Detection by a faithful test point
in a common target chart then identifies the complete strong maps.
This implemented proof retains the explicit domain completed-residue
comparison.

The provenance is internal, from the actual strong-map pullback,
kernel-quotient descent, full-field-point functoriality and the
common-chart detection theorem. This module makes no
claim to the final unconditional localized pullback preservation.
