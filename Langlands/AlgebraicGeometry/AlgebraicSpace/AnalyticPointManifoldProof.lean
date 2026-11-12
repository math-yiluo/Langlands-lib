import Langlands.AlgebraicGeometry.AlgebraicSpace.AnalyticPointManifoldStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.AnalyticPointUniqueness

/-!
# Conrad's analytic manifold assertion

Combine the canonical admissible analytic family with uniqueness on actual rational points.
-/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Conrad's Proposition 5.4, analytic-manifold assertion. -/
theorem analyticPointManifold : AnalyticPointManifoldStatement.{u} := by
  intro K _ _
  exact ⟨⟨canonicalAnalyticPointStructure K, canonicalAnalyticPointStructure_isAdmissible K⟩,
    fun σ τ hσ hτ => AnalyticPointStructure.equivalent_of_isAdmissible σ τ hσ hτ⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
