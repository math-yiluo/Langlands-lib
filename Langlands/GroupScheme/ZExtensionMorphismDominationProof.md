# Morphism-compatible domination of actual z-extensions

`zExtensionMorphismDomination` proves the unchanged proposition
`ZExtensionMorphismDominationStatement` over every field. Its input consists
of connected reductive groups, their supplied actual z-extensions, and an
arbitrary homomorphism between the original groups. The construction is the
fiber product used in Kaletha–Prasad, Lemma 11.4.3, printed pages 428–429
(PDF pages 459–460).

Take the actual pullback of the composite from the source extension to the
target group and the projection from the target extension. Its projection
to the original source group has the product of the two supplied induced
tori as its full scheme-theoretic kernel. Inducedness of this product follows
from `IsInducedTorus.of_product_iso`. The pullback geometry API supplies a
closed central kernel inclusion, fppf exactness, and an affine source.
`IsConnectedReductive.of_torusKernel` then gives connected reductivity of
the source.

The first pullback projection is surjective and has central kernel.
`HasSimplyConnectedDerivedGroup.of_centralSurjection` lifts the supplied
simple connectedness of the source extension's derived group to the new
source. These properties fill the original `IsZExtension` structure without
changing its meaning. The two actual pullback projections give the required
maps, with the first equality by construction and the second by the
pullback square. No splitting, characteristic, perfectness, or local-field
hypothesis enters the proof.
