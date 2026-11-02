# Stalk bases and relative flatness of actual line bundles

This internal construction concerns actual scheme-module sheaves. For every
scheme, `IsLocallyFreeRankOne.stalkLinearEquiv` constructs a linear equivalence
between each stalk of an actual locally free rank-one sheaf and the local
ring, using the canonical local-ring module action.

At the given point the proof chooses an open neighborhood and an actual
isomorphism of the restricted module sheaf with the unit module sheaf.
The induced stalk isomorphism followed by `unitStalkLinearEquiv` gives the
rank-one basis on this open. `ofRestrictStalkRankOneEquiv` transports that
basis to the original point and its original local ring.

`IsLocallyFreeRankOne.relativeStalkLinearEquiv` regards this same additive
equivalence as linear over a base local ring by restricting both scalar
actions along the actual structure-map stalk homomorphism. Its linearity
is exactly the local-ring linearity of the constructed basis.

For a flat morphism `f`, Mathlib's `Flat.stalkMap` says that the source local
ring is flat over the base local ring. Transferring flatness along the
relative linear equivalence proves `IsLocallyFreeRankOne.isFlatOver`.
`LineBundle.isFlatOver` applies this result to the actual underlying sheaf
of a line bundle.

The constructions are uniform in the universe, scheme, and point. The
relative flatness results require precisely flatness of `f`, and do not
assume a field, properness, or finite presentation. This elementary
prerequisite does not assert the existence of a Picard-stack atlas.
