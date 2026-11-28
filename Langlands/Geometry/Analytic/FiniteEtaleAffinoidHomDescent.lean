import Langlands.Geometry.Analytic.FiniteEtaleChartImageReduction
import Langlands.Geometry.Analytic.FiniteEtaleRationalImage

/-! # Descent of analytic morphisms along finite étale affinoid covers -/

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

/-- A finite étale surjection of small affinoid spectra is effective for
descent of morphisms to any localized target. -/
theorem finiteEtaleAffinoidHomDescent : FiniteEtaleAffinoidHomDescentStatement.{u, v} := by
  apply finiteEtaleAffinoidHomDescent_of_rationalImages
  intro K _ _ _ A B _ _ f hf he D
  exact isOriginalChartDomain_image_rational f hf he D

end Langlands.Analytic.SaturatedAtlasPresentation
