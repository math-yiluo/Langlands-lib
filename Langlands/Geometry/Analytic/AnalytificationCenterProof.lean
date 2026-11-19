import Langlands.Geometry.Analytic.AnalytificationCenterComparison
import Langlands.Geometry.Analytic.SchemeAnalytificationBasicOpenRangeProof
import Langlands.Geometry.Analytic.AffineAnalytificationSeminormProof
import Langlands.Geometry.Analytic.AffineAnalytificationCenterSurjectivityProof
import Langlands.Geometry.Analytic.FiniteTypeDomainNormExtensionProof

/-! # Surjectivity and rational fibres of the analytification center maps -/

noncomputable section

universe u v

namespace Langlands.Analytic.SchemeAnalytification

/-- The affine and scheme center maps are surjective, have singleton rational
fibres, and satisfy the rational-center and affine-chart formulas. -/
theorem analytificationCenter : AnalytificationCenterStatement.{u, v} := by
  constructor
  · intro K _ _ _ A _ _ P
    refine ⟨AffineAnalytification.CenterSurjectivity.center_surjective_of_finiteType_norms
      K P (AffineAnalytification.SeminormComparison.range_pointSeminorm K P)
      (AffineAnalytification.finiteTypeDomainNormExtension.{u, v} K),
      AffineAnalytification.CenterComparison.mem_center_analyticPoint K P, ?_⟩
    exact AffineAnalytification.CenterComparison.eq_analyticPoint_of_center_eq K P
      (AffineAnalytification.SeminormComparison.pointSeminorm_injective K P)
  · intro K _ _ _ X f _
    have hrange := OpenGluing.range_ι K f
    refine ⟨CenterComparison.center_surjective_of_affine K f ?_, hrange,
      CenterComparison.center_analyticRationalPoint K f, ?_⟩
    · intro U
      exact AffineAnalytification.CenterSurjectivity.center_surjective_of_finiteType_norms
        K (chartPresentation K f U)
        (AffineAnalytification.SeminormComparison.range_pointSeminorm K (chartPresentation K f U))
        (AffineAnalytification.finiteTypeDomainNormExtension.{u, u} K)
    · exact CenterComparison.eq_analyticRationalPoint_of_center_eq K f hrange
        (fun U => AffineAnalytification.SeminormComparison.pointSeminorm_injective K
          (chartPresentation K f U))

end Langlands.Analytic.SchemeAnalytification
