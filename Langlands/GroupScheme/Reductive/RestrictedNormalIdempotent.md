# The ring idempotent for a restricted natural normal idempotent

For a reductive group with almost-simple geometric fibres, a natural
idempotent transformation on the group functor restricted to algebras under
`T`, commuting with conjugation on all such algebras, determines an actual
ring idempotent of `T`. `RestrictedAffinePoints.ringDecomposition` constructs
it by reconstructing the actual endomorphism of `G_T`, proving full
scheme-test normality, and applying the actual clopen and ring decomposition.
Almost-simple geometric fibres are preserved under this arbitrary base
change.

On every original object under `T` where the ring idempotent becomes one,
the original transformation is the identity; where it becomes zero, it is
trivial. The exact original point comparison identifies the transformation
with the reconstructed map. Pullback point equivalences translate the
actual identity or zero map after coefficient change back to the original
coefficient points.

For every original coefficient algebra `X`, the two quotients by
`1 - X(e)` and `X(e)` remain objects under `T` with their original composite
structure maps. In them the constructed element becomes one and zero,
respectively. Naturality of the original transformation and the preceding
two conclusions give exactly the universal quotient-point formulas.
`projectionData` bundles this actual element, its idempotence and those
formulas, supplying the existence part of the relative normal-idempotent
statement.

All coefficient rings and scheme tests are retained, including nonreduced
ones and zero rings. The construction is internal. Uniqueness of the ring
idempotent is a separate assertion, proved in
`Reductive.RelativeAlmostSimpleNormalIdempotentProof`.
