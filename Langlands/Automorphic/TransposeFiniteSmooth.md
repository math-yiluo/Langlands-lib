# Inverse-transpose pullback on actual finite-smooth adelic functions

This internal construction for the proof of
`CuspidalTransposeInverseContragredientStatement` combines the ambient rational
continuous pullback of `TransposeAmbient` with the archimedean smooth pullback and
differential covariance of `Global/ArchimedeanTransposeSmooth`.

`finiteSmoothTranspose K n` is the complex-linear involution
`f(g) ↦ f((g⁻¹)ᵀ)` on the actual finite-smooth rational function space.
Smoothness of every archimedean slice follows by applying
`ArchimedeanGL.smoothTranspose`; the finite argument is reindexed by inverse
transpose. The common open finite stabilizer is preserved by the ambient
pullback. This construction asserts existence of an open finite stabilizer;
it does not assert compactness of that stabilizer.

Full adelic translation, and in particular finite adelic translation, is
twisted by the same group automorphism. The genuine enveloping algebra
action is twisted by `envelopingIota`. This follows by comparing every
finite slice and using the proved archimedean covariance. Restricting to
the actual center gives center covariance.

The complete center-orbit span of the transformed actual adelic function
is exactly the image of the original span under the pullback equivalence.
The proof compares the generating sets using the involution `centerIota`.
Consequently the common center-orbit spaces are linearly equivalent and
simultaneous center finiteness is preserved and reflected. This is a
common-family result, not merely separate center finiteness of each slice.

No growth, compact finiteness, cuspidality or contragredient identification
is asserted here. `CuspidalTransposeInverseContragredientStatement` is proved as
`cuspidalTransposeInverseContragredient` in
`Global/RankinSelberg/CuspidalTransposeInverseContragredientProof`.
