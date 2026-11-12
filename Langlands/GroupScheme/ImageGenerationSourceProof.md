# Proof of `Langlands.GroupScheme.ImageGenerationSourceStatement`

This module proves the published proposition `Langlands.GroupScheme.ImageGenerationSourceStatement` (module `Langlands.GroupScheme.ImageGenerationStatement`) at every universe `u`. The statement is the conjunction of `SmoothConnectedAffineGeometryStatement`, `PointedImageGenerationStatement` and `PointedImageEnvelopeStabilityStatement`.

The theorem is `Langlands.GroupScheme.imageGenerationSource : ImageGenerationSourceStatement.{u}`, with no hypotheses.

## Proof

The proof term is the anonymous constructor applied to the published proofs of the three conjuncts.

The theorem adds no mathematics; it names a combination of published results.

## Published inputs

- `Langlands.GroupScheme.smoothConnectedAffineGeometry` (module `Langlands.GroupScheme.SmoothConnectedGeometryProof`)
- `Langlands.GroupScheme.ImageGeneration.pointedImageGeneration` (module `Langlands.GroupScheme.ImageGenerationPointed`)
- `Langlands.GroupScheme.pointedImageEnvelopeStability` (module `Langlands.GroupScheme.ImageEnvelopeStabilityProof`)
