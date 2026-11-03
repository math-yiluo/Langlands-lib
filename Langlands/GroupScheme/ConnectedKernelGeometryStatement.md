# Geometric connectedness from the actual group kernel

`Langlands.GroupScheme.ConnectedKernelHomGeometryStatement` states that an
actual group-scheme homomorphism `q : G → Q` over an arbitrary scheme `S`
is geometrically connected whenever its underlying scheme morphism is
surjective and the structure morphism `ker(q) → S` of its actual scheme
kernel is geometrically connected.

The kernel is the existing pullback of `q` along the target identity section.
Surjectivity is surjectivity on underlying scheme points, and geometric
connectedness is Mathlib's condition on every field-valued base change.
All schemes have arbitrary universe `u`. No field-base, commutativity,
smoothness, finite-type, or affineness premise occurs.

This is an internal proposition target. The intended proof uses the actual
isomorphism `G ×[S] ker(q) ≅ G ×[Q] G` and descent of geometric connectedness
along the surjective base change `q`. The declaration does not include that
proof. In the parent unipotent-radical quotient task it will imply connectedness
of inverse images under a smooth quotient with a connected finite-type kernel.
It makes no quotient-existence or pseudo-reductivity assertion.
