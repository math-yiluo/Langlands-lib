import Langlands.Geometry.Analytic.SchemeAnalytificationGluingStatement
import Langlands.Geometry.Analytic.SchemeAnalytificationOpenGluing
import Langlands.Geometry.Analytic.SchemeAnalytificationSeparatedProof

/-! # Scheme analytification gluing and separatedness -/

universe u

namespace Langlands.Analytic.SchemeAnalytification

/-- Scheme analytification satisfies open gluing, and its glued space is
Hausdorff exactly when the structure morphism is separated. -/
theorem schemeAnalytificationGluing : SchemeAnalytificationGluingStatement.{u} := by
  intro K _ _ _ X f _
  obtain ⟨localEmbedding, chartEmbedding, overlap, topHomeomorphism⟩ :=
    OpenGluing.affineOpenGluing K f
  exact ⟨localEmbedding, chartEmbedding, overlap, topHomeomorphism,
    schemeAnalytificationSeparated K X f⟩

end Langlands.Analytic.SchemeAnalytification
