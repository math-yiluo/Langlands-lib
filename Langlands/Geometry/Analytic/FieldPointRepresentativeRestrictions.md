# Restriction and common refinement of faithful local representatives

This internal construction works over a complete ultrametric normed
field `K` with a complete normed extension field `L`. The algebra,
space and extension-field universes are independent. The target is
a saturated presentation with space and chart-index universes both
equal to the space universe, as in `LocalizedEtaleFieldPointPullbackStatement`.

For nested actual charts `i` and `j` containing the same full field
point `p`, the actual bounded restriction map preserves the exact
evaluations. This is bounded-algebra-hom extensionality applied to
the restriction compatibility stored in `p`; that identity itself
does not require completeness of `L`.

Descending this restriction through the two actual evaluation
kernels defines `p.chartTestRestriction`, a strong map from the
faithful representative at the smaller chart `i` to the faithful
representative at the larger chart `j`. Both chart spectra are small
because their chart maps are injective into the original space.
The construction uses the actual local evaluation kernels afresh.

Under the explicit domain completed-residue comparison, the full
faithful test point at `i` maps to the full faithful test point at `j`.
The existing quotient-map naturality gives this equality of all
chart evaluations and their restriction compatibility.

Composing the restriction map with the representative map at `j`
equals the representative map at `i`, as complete strong morphisms
into the original saturated presentation. Both maps land in the
common chart `j`. Their full test-point images agree by full-point
functoriality and the representative-image identities, so the
common-chart detection theorem gives the claimed equality.
This proof retains the explicit domain completed-residue comparison.

The atlas net axiom provides a containing subchart inside the
intersection of any two charts containing `p`. Its faithful
representative maps to both original representatives. These maps
preserve their full test points and commute over the original
target, giving `exists_chartTest_common_refinement`.

The provenance is internal: bounded evaluation compatibility,
actual character-kernel quotient descent and the atlas net axiom
give the constructions, and faithful common-chart detection gives
the triangles. This module asserts no final unconditional localized
pullback preservation.
