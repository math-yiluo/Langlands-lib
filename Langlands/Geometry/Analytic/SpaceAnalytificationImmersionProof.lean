import Langlands.Geometry.Analytic.SpaceAnalytificationClosedImmersionReduction
import Langlands.Geometry.Analytic.AffineAnalytificationImmersionProof

/-! # Analytification of algebraic-space immersions on underlying spaces -/

universe u

namespace Langlands.Analytic.SpaceAnalytification

/-- Analytification carries open and closed immersions of separated algebraic spaces
locally of finite type to open and closed embeddings of underlying analytic spaces. -/
theorem spaceAnalytificationImmersion : SpaceAnalytificationImmersionStatement.{u} := by
  apply spaceAnalytificationImmersionReduction
  intro K _ _ _
  exact affineClosedEmbeddingProperty_of_statement
    AffineAnalytification.affineAnalytificationImmersion

end Langlands.Analytic.SpaceAnalytification
