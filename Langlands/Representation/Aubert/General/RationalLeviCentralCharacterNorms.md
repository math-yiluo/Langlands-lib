# Moduli of characters on actual Levi-central torus points

This internal construction uses the literal rational torus map and the full
abstract center of the literal standard Levi. It introduces no external
source assertion.

The natural homomorphism `leviCentralTorusPointToCenter` sends an actual
torus point in `leviCentralTorusPoints` to the same ambient point, viewed
in the Levi and its full abstract center. Since all torus points already
lie in the Levi, the domain subgroup is the inverse image of the ambient
centralizer of the Levi. With the canonical point topologies, the natural homomorphism is
continuous for any topology on the field, assuming the torus and ambient
group are affine. If the ambient rational points are a Hausdorff
topological group, the domain subgroup is closed.

An open-kernel complex character of the full Levi center therefore pulls
back to an open-kernel character on this torus-point subgroup. If the
torus is split, its common rational-character norm kernel is compact.
Intersecting that compact group with the closed central torus-point
subgroup remains compact. The positive modulus of a smooth character on
a compact group is trivial, so the given character has norm one on this
intersection. No scheme-center comparison is used.

The field has arbitrary universe `u`. The compact-kernel theorem assumes
a nonarchimedean local field, an affine split torus, a Hausdorff ambient
topological group and an open character kernel. These results prove no
sign trichotomy, strict exponent condition or self-association theorem.
