# Closed positive-real subgroups in the actual adelic point topology

Worker 112, with unchanged actual-point topology support by Worker 94.

This is an internal consequence of the intrinsic positive-real subgroup,
the proved scalar closed embedding, and the actual regular-function point
topology. It uses the same scheme-point carrier and group operations as
`PositiveRealTorusIntrinsic`; it adds no topology by transport from a chosen
splitting.

The local topology instance on the `Lie.AffinePoints` alias is definitionally
the existing `GroupScheme.affinePointsTopologicalSpace`; it only makes that
canonical topology visible to instance search.

For a commutative group scheme `T` over a field `F` and a topological
coefficient algebra `A`, `continuous_characterHom` proves continuity of the
existing actual algebraic-character evaluation. The proof composes continuous
postcomposition by the group-scheme character with the existing continuous
map from actual multiplicative-group points to coefficient units. Both the
unit and its inverse are regular functions, which is why the codomain has
the units topology. `continuousCharacter` bundles this continuous
homomorphism. No topology on `F`, affineness of `T`, or continuity of the
coefficient ring operations is needed for these assertions.

Over any number field `F`, every inverse image of the positive scalar idele
subgroup under one of these characters is closed. Their intersection is
exactly `intrinsicSubgroup F T`, so `isClosed_intrinsicSubgroup` follows.
`closedIntrinsicSubgroup` records that subgroup with its proved closedness.
For any supplied finite splitting, `isClosed_subgroup` uses the previously
proved equality of the coordinate subgroup with the intrinsic subgroup.
The empty-rank case is included.

This proof of closedness uses character inverse images. It does not require
an inverse-continuity assertion for the torus coordinate equivalence, and
does not assert continuity of the positive torus parametrization. A
coordinate homeomorphism, closedness of an image in an arbitrary ambient
group, a central split-torus selection, and reduction or volume results
remain separate obligations.
