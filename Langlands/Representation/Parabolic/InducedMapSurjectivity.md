# Surjectivity of normalized parabolic and product maps

The declarations `Langlands.Classification.normalizedParabolicMap_surjective`
and `normalizedProductMap_surjective` are the unchanged proof adapters extracted
from [SegmentHeadProductCuspidalSupportProof](../Classification/SegmentHeadProductCuspidalSupportProof.md).
They are now shared by that proof and
[SegmentEdgeMaps](../Classification/SegmentEdgeMaps.md).

For smooth complex representations of the actual block Levi of `GL_n` over a
p-adic field, normalized parabolic induction sends a supplied surjective
intertwiner to a surjective induced map. The proof applies the published smooth
induction surjectivity theorem, using compact open subgroups, closedness of the
parabolic, and smoothness of the twisted inflations.

The product version applies the published external tensor-map surjectivity
theorem and then the parabolic adapter. Both endpoint representation families
have the same carrier universe. No segment or cuspidal-support hypothesis is
used.
