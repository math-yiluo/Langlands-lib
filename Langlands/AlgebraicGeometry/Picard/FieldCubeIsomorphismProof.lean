import Langlands.AlgebraicGeometry.Picard.FieldCubeIsomorphismStatement
import Langlands.AlgebraicGeometry.Picard.FieldCubeTrivialityProof
import Langlands.AlgebraicGeometry.Picard.CubeIsomorphismAssembly
import Langlands.AlgebraicGeometry.Picard.LocalComparisonProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof

/-! # The two-line-bundle isomorphism form of the geometric cube theorem

The published geometric cube theorem and tensor comparison proofs discharge
the three prerequisites of the algebraic isomorphism assembly.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Two line bundles on a pointed product of three smooth proper geometrically
connected schemes over a field are isomorphic if their three face restrictions
are isomorphic. -/
theorem fieldCubeIsomorphism : FieldCubeIsomorphismStatement.{u} := by
  intro K _ X Y Z hXs hXp hXc hYs hYp hYc hZs hZp hZc x₀ y₀ z₀ L M
    ⟨e₁⟩ ⟨e₂⟩ ⟨e₃⟩
  exact ⟨lineBundleIsoOfThreePullbackComparisons (locallyFreeRankOneIffTensorInvertible _)
    Langlands.Scheme.Modules.pullbackTensorComparisonIsIso
    (CubeFace.first X Y Z x₀).left (CubeFace.second X Y Z y₀).left
    (CubeFace.third X Y Z z₀).left
    (fieldCubeTriviality K X Y Z hXs hXp hXc hYs hYp hYc hZs hZp hZc x₀ y₀ z₀)
    L M e₁ e₂ e₃⟩

end Langlands.AlgebraicGeometry.Picard
