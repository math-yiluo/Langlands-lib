# Geometric assembly for a dominant generated subgroup

This internal adapter supplies the geometric conclusion of pointed-image
generation from a separately constructed closed subgroup. It is derived from
`ImageGenerationDominant` and Mathlib's theorem `smooth_of_grpObj`; it makes no
new assertion of existence of a stabilized product closure.

Work over any field `k` in universe `u`. Let `G` be an affine group scheme
locally of finite type over `k`, let `i : H ⟶ G` be a closed subgroup inclusion,
and let `g : V ⟶ H.X` factor the original morphism `f`. Suppose `H` is
geometrically reduced and geometrically irreducible, and for some strictly
positive `n`, the actual ordered product `orderedPowerMap g n` is dominant.
`GeneratedImage.ofGeometricPower` returns an actual `GeneratedImage f` together
with `HasSmoothConnectedGeneration`.

The implemented proof obtains affineness and local finite type of `H` by
composition of its closed immersion with the structure map of `G`. Geometric
reducedness over a field implies reducedness, so the dominant-product adapter
identifies `H` with the fixed closed envelope. Mathlib's `smooth_of_grpObj`
proves smoothness from the actual group structure, local finite type, and
geometric reducedness over the arbitrary field. Geometric irreducibility implies
connectedness after every field base change, which gives geometric
connectedness. The factor and power-map identifications in the previous adapter
preserve the given positive dominant product.

The published arbitrary-base theorem
`AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected`, reused
from its attributed Anthropic FLT port, supplies the irreducible-to-connected
implication on every field pullback. No perfectness,
separability, characteristic condition, or reducedness of closed subgroup
competitors is imposed. Construction of `H` with the stated geometric
properties and positive dominant product remains a separate obligation.
