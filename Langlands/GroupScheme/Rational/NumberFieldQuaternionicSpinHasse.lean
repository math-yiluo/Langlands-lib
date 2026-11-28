import Langlands.GroupScheme.Rational.NumberFieldQuaternionicNormOneIsometryHasse
import Langlands.GroupScheme.Rational.NumberFieldQuaternionicSpinKernelHasseProof

/-! # The Hasse kernel for quaternionic spin groups over number fields -/

universe u

namespace Langlands.GroupScheme

/-- A cocycle for the spin cover of a nondegenerate rank-at-least-four quadratic form over
a central quaternion division algebra with orthogonal involution over a number field is
trivial on its finite Galois cover if it is trivial after pullback to every completion. -/
theorem numberFieldQuaternionicSpinHasse : NumberFieldQuaternionicSpinHasseStatement.{u} :=
  numberFieldQuaternionicSpinHasse_of_kernels
    numberFieldQuaternionicNormOneIsometryHasse numberFieldQuaternionicSpinKernelHasse

end Langlands.GroupScheme
