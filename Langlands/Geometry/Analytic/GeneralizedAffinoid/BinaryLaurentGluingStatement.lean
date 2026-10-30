import Langlands.Geometry.Analytic.GeneralizedAffinoid.BinaryLaurentDiagram
import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictComparison

/-! # Scalar descent for the actual relative binary Laurent diagram -/

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.BinaryLaurent

/-- Over a complete nontrivially normed ultrametric field, scalar sections of
the actual relative upper and lower Laurent quotients of a presented strict
base whose images in the actual two-variable overlap quotient agree descend
uniquely to the base. -/
def GluingStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
    (∃ c : K, 1 < ‖c‖) →
    ∀ (P : PresentedStrictAffinoidAlgebra K)
      (f : PresentedAffinoidAlgebra.ofStrict K P)
      (sUpper : Upper K (PresentedAffinoidAlgebra.ofStrict K P) f)
      (sLower : Lower K (PresentedAffinoidAlgebra.ofStrict K P) f),
      left K (PresentedAffinoidAlgebra.ofStrict K P) f sUpper =
          right K (PresentedAffinoidAlgebra.ofStrict K P) f sLower →
        ∃! a : PresentedAffinoidAlgebra.ofStrict K P,
          upperBase K (PresentedAffinoidAlgebra.ofStrict K P) f a = sUpper ∧
            lowerBase K (PresentedAffinoidAlgebra.ofStrict K P) f a = sLower

end Langlands.Analytic.PresentedAffinoidAlgebra.BinaryLaurent
