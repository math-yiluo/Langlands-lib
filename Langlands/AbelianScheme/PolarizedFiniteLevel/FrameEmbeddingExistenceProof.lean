import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingReduction
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFieldEmbeddingProof

/-!
# Existence of frame-normalized cubic embeddings

A proof of `Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingExistenceStatement`: the
Library's proved definition `frameEmbeddingExistence_of_cubicFieldEmbedding` (frame-normalized
cubic embeddings from Lefschetz's theorem over fields) applied to the cubic Lefschetz embedding
`cubicFieldEmbedding`. See the paired Markdown.
-/

universe u

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- **Frame-normalized cubic embeddings.** Over a locally noetherian base, every datum with
`0 < d` whose projective frame locus for a family `ρ` of `6^g*d + 1` level coefficient tuples is
the whole base has a frame-normalized cubic embedding for `ρ` into relative projective
`cubicProjectiveDimension g d`-space. -/
theorem frameEmbeddingExistence : FrameEmbeddingExistenceStatement.{u} :=
  frameEmbeddingExistence_of_cubicFieldEmbedding cubicFieldEmbedding

end Langlands.AbelianScheme.PolarizedFiniteLevel
