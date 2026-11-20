# Complex embedding coordinates of the archimedean Lie algebra

For a totally complex number field, `complexEmbeddingIndex` identifies the Library's embedding index with the complex places paired with `Fin 2`. Side zero gives the place coordinate and side one gives its complex conjugate. The real-place branch is empty by total complexity.

`complexEmbeddingLieCoordinates` combines the actual per-place Lie projections with the two-coordinate complexification of the underlying real matrix Lie algebra. Its inverse applies the local inverse to each pair and sums the place inclusions. The two inverse laws use the real place decomposition after eliminating the empty real-place sum, and the projection relations for equal and distinct complex places.

`complexEmbeddingLieCoordinates_complexify` identifies every entry of the image of a real matrix direction with `embeddingComponent` applied to the corresponding entry of the actual archimedean matrix. This aligns the split with the diagonal weights used in `IsHighestWeightVector`.

This coordinate interface is derived from the Library's actual archimedean Lie algebra and `ComplexGenericLarge.tensorLieEquiv`. It supplies the identification used for the totally complex infinitesimal-character bridge.
