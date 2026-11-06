import Langlands.GroupScheme.RelativeParabolicQuotientAssembly
import Langlands.AlgebraicGeometry.ProperOfFibres.Criterion

/-! # Proof of the generic proper-ambient criterion of the relative parabolic quotient assembly -/

set_option autoImplicit false

universe u

namespace Langlands.GroupScheme.RelativeParabolicQuotient

/-- The generic properness implication consumed by the relative parabolic quotient
assembly holds over every base scheme. -/
theorem properAmbientCriterion_holds : ProperAmbientCriterion.{u} :=
  Langlands.AlgebraicGeometry.ProperOfFibres.properAmbientCriterion

end Langlands.GroupScheme.RelativeParabolicQuotient
