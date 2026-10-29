import Langlands.Geometry.Analytic.Affinoid

/-! # The quotient norm of the unit in a strict affinoid presentation

Extracted unchanged from `StrictTestDomain.RationalSectionContinuityProof`.
-/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedStrictAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- The quotient norm of the unit is at most one, also in a zero quotient. -/
theorem quotient_norm_one_le (A : PresentedStrictAffinoidAlgebra K) :
    ‖(1 : A)‖ ≤ 1 := by
  exact (Ideal.Quotient.norm_mk_le A.ideal
    (1 : StrictTateAlgebra (Fin A.arity) K)).trans_eq norm_one

end Langlands.Analytic.PresentedStrictAffinoidAlgebra
