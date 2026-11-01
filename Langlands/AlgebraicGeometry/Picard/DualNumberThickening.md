# The topology of the actual dual-number thickening

For a scheme `X` over an arbitrary field `k`, `DualNumberThickening.thickening f`
is the actual scheme pullback of `f` along `dualNumberProjection k`.
Its maps `projection` and `structureMap` are the two limit projections.
`closedPoint` is the actual map from `X` induced by the identity and the field
augmentation, with both projection equations proved.

The field augmentation is a surjective closed immersion. Surjectivity of its
ring map gives closed immersion. For surjectivity on points, the range of the
spectrum map is the vanishing locus of its kernel. Every kernel element has
zero first coordinate and is nilpotent, so belongs to every prime ideal.

`closedPoint_isPullback` identifies the square of the zero section with the
actual augmentation as a pullback, using cancellation of a pullback square
against the identity square. Stability under base change then proves that
`closedPoint` is also a surjective closed immersion for arbitrary `X`.

The projection is a retraction of the zero section as a scheme morphism.
Surjectivity of the zero section proves the other inverse identity on points.
These actual point maps, with their continuity, define
`underlyingHomeomorph : thickening f ≃ₜ X`. The order isomorphism `opensEquiv`
sends an open of `X` to its inverse image under the projection; its inverse
uses inverse image under the zero section.

This is an internal construction from scheme pullbacks, the split dual-number
ring, and the spectrum range theorem. It does not identify the structure
sheaf of the thickening, classify line bundles, or assert a cohomology
comparison. Those are further obligations of the tangent-to-H1 construction.
