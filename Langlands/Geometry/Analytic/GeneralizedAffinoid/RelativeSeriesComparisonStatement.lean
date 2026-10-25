import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeSeriesMap

/-! # Isometric comparison with relative weighted restricted series: target -/

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Adjoin

/-- The actual forward map is a surjective isometry, and the kernel of
evaluation before quotienting is exactly the closed ideal of old relations.
The coefficient field is complete; arbitrary positive finite polyradii,
empty variable blocks and zero quotients are allowed. -/
def RelativeSeriesComparisonStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : PresentedAffinoidAlgebra K) (m : ℕ) (s : PositivePolyradius (Fin m)),
    Function.Surjective (relativeSeriesMap K A s) ∧
    Isometry (relativeSeriesMap K A s) ∧
    (∀ f : GeneralizedTateAlgebra (A.polyradius.append s) K,
      relativeSeriesEvaluation K A s f = 0 ↔
        f ∈ (algebra K A s ∅).ideal)

end Langlands.Analytic.PresentedAffinoidAlgebra.Adjoin
