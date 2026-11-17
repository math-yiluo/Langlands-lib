# Actual transitions between affine pinned charts

This internal construction compares the actual affine pinned models of one
original group on an arbitrary common test scheme. Both chart pullbacks are
identified with the direct pullback of the original group, using the actual
pullback-composition isomorphisms and the supplied equalities of base maps.
Their composite is `affineFrameComparison`.

The transition fixes the original normalized coordinate torus exactly and
therefore respects the canonical positive-coroot cocharacter of the supplied
base. If the supplied actual affine root frames are coherent, it also matches
the same simple pinning vectors on every affine coefficient test. The proof
projects both dual-number points to the original group, applies frame coherence
on each chart, and identifies the two direct test maps by their common
factorization. Equality of the base projections completes equality in the
actual pullback group.

There is no assumption that the common test scheme or any chart intersection
is affine. Root frames and their coefficient-extension coherence are supplied
structural data; their construction from actual line bundles and the Picard
hypothesis remains a separate prerequisite.
