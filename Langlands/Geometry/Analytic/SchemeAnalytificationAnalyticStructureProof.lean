import Langlands.Geometry.Analytic.SchemeAnalytificationAnalyticStructure
import Langlands.Geometry.Analytic.SchemeAnalytificationOpenGluing

/-! # The glued analytification of a scheme carries an analytic structure

This module proves `SchemeAnalytificationAnalyticStructureStatement` by combining the
conditional construction `analyticStructure_of_openGluing` with the unconditional open-gluing
theorems `OpenGluing.isOpenEmbedding_ι` and `OpenGluing.range_ι_inter`. -/

universe u

namespace Langlands.Analytic.SchemeAnalytification

/-- The glued analytification of every scheme locally of finite type over a complete
nonarchimedean field carries an analytic structure glued from the affine analytifications. -/
theorem schemeAnalytificationAnalyticStructure :
    SchemeAnalytificationAnalyticStructureStatement.{u} := by
  intro K _ _ _ X f _
  exact analyticStructure_of_openGluing
    ⟨OpenGluing.isOpenEmbedding_ι K f, OpenGluing.range_ι_inter K f⟩

end Langlands.Analytic.SchemeAnalytification
