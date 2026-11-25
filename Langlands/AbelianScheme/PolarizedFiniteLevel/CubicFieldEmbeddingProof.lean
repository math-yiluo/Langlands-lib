import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFieldEmbeddingReduction
import Langlands.AbelianScheme.AlgClosedFieldAmpleCubeSeparationProof

/-!
# The cubic Lefschetz embedding of an ordinary polarized datum over a field

A proof of `Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFieldEmbeddingStatement`: the
Library's reduction to algebraically closed fields, `cubicFieldEmbedding_of_cubeSeparation`,
applied to Lefschetz separation by the cube of an ample line bundle over an algebraically closed
field (`Langlands.AbelianScheme.algClosedFieldAmpleCubeSeparation`). See the paired Markdown.
-/

universe u

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- **Lefschetz's theorem for the canonical cubic bundle (Mumford, *Abelian Varieties*, §17).**
For an actual ordinary polarized datum over a field with `0 < d`, the complete linear system of
the canonical cubic bundle has no base points, and the morphism to projective space given by any
basis of its global sections is a closed immersion. -/
theorem cubicFieldEmbedding : CubicFieldEmbeddingStatement.{u} :=
  cubicFieldEmbedding_of_cubeSeparation algClosedFieldAmpleCubeSeparation

end Langlands.AbelianScheme.PolarizedFiniteLevel
