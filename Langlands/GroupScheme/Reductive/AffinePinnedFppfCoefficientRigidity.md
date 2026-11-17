# Detecting pinning units through an fppf cover

This internal helper strengthens coefficient detection to fppf-local concrete
pinning for the identity pullback of an actual affine-model automorphism.
When the differential of a chosen original simple vector is a unit times
another chosen original simple vector, that unit is one in the original ring.

For any scheme where the actual base-changed automorphism preserves local
pinning, projection of its dual-number pinning points gives the original
coefficient-extended differential. The simple-vector scalar rigidity theorem
forces the scalar image to be one on each local coefficient test over that
scheme. Naturality of pullback composition identifies normalized two-step
pullback with direct base change of the original automorphism.

The construction `directFppfPinningCover` chooses this direct-base-change
cover from the supplied fppf-local pinning hypothesis. Its
`DirectFppfPinningCover` data retain the actual covering scheme, projection,
flatness, surjectivity, finite-presentation property, and local pinning clause.
The unit-rigidity proof uses that constructed cover.

The detection argument works over any flat surjective cover. Regard the
original unit as an actual point of the multiplicative group. Local-ring tests
detect its equality with the identity after pullback to the cover, including
nilpotent structure. A flat surjective scheme morphism is an epimorphism, so
this equality descends to the original base, where the affine-points
equivalence recovers the original unit.

No connectedness or reducedness is assumed, and the covering scheme need not
be affine. The fppf-local application uses the supplied pinning cover; existence
of such a cover and of pinned representatives remains a separate input.
