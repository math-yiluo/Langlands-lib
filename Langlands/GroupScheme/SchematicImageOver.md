# Schematic images of morphisms over a scheme

For a morphism of schemes over a common base, the scheme-theoretic image is
viewed over that base by composing its closed immersion with the original
target's structure morphism. The original morphism factors through this closed
immersion. If the original morphism is quasi-compact, its projection to the image
is quasi-compact and schematically dominant. Preimages of affine opens of the
original target cover the image by affine opens, and the projection is injective
on sections over each of these opens.

A quasi-compact flat surjection is schematically dominant by injectivity on
sections over every affine open of its target. Pulling back a morphism over a
common base gives a cartesian square on the underlying schemes by pullback
cancellation. Two closed schematically dominant factorizations of a fixed map
are compared by lifting each inclusion through the other using schematic
dominance. Cancellation at the closed immersions shows that the two lifted
maps are inverse and that the comparison commutes with both factorizations.

This internal construction packages the existing scheme-theoretic image and
closed-factorization APIs for the arbitrary-base torus image argument.

The projection uses schematic dominance of the map to the image. Its base-change square is `HomIsogeny.baseChange_isPullback`.
