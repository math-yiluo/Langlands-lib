import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceAnalyticManifoldStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceDimensionAnalyticAssemblyProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceDimensionAnalyticFunctorialityProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceDimensionEtaleAnalyticIsoProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceDimensionAffineAgreement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceDimensionAnalyticUniquenessProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.AnalyticAffineNormalization
import Langlands.AlgebraicGeometry.PointTopology.CompleteHenselianValuedFieldProof

/-! # Conrad's varying-dimension analytic manifold assertion -/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Over every complete nontrivially normed field, the canonical
pure-dimensional family assembles into an admissible varying-dimension
analytic structure, unique up to analytic identity in both directions. -/
theorem smoothSourceAnalyticManifold :
    SmoothSourceAnalyticManifoldStatement.{u} := by
  intro K _ _
  let hK := PointTopology.completeHenselianValuedField K
  let σ := canonicalAnalyticPointStructure K
  have hσ : σ.IsAdmissible := canonicalAnalyticPointStructure_isAdmissible K
  refine ⟨⟨σ.dimensionStructure hK, ?_⟩, ?_⟩
  · exact ⟨smoothSourceDimensionAnalyticAssembly K hK σ hσ.1,
      smoothSourceDimensionAnalyticFunctoriality K hK σ hσ,
      smoothSourceDimensionEtaleAnalyticIso K hK σ hσ,
      smoothSourceDimensionAffineAgreement K hK σ hσ⟩
  · exact smoothSourceDimensionAnalyticUniqueness K

end Langlands.AlgebraicGeometry.AlgebraicSpace
