import Langlands.GroupScheme.RelativeLevi.SplitBorelVectorSeriesAssembly
import Langlands.GroupScheme.Reductive.GlobalSplitRootParametrization

/-! # Split Borel structure with a finite affine vector-quotient kernel series -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The full split Borel structural statement over every commutative ring. -/
theorem splitBorelVectorSeries : SplitBorelVectorSeriesStatement.{u} := by
  intro R _ G hG I _ t J P
  letI := hG.isAffineHom
  intro ht hmax hP hfree
  exact hasSplitBorelVectorSeries_of_rootParametrizations_and_chartSeries
    hG ht hmax hP
    (LocalRootGroup.rootParametrizationsOfFreeWeights t hG hmax hP hfree)
    (LocalRootGroup.isRootParametrization_rootParametrizationsOfFreeWeights
      t hG hmax hP hfree)
    (fun c => c.toRootHeightChart.hasFiniteAffineVectorSeries)

end Langlands.GroupScheme
