import Langlands.GroupScheme.Rational.QuaternionicSpinKernelMu
import Langlands.GroupScheme.Rational.QuaternionicSpinLineSimilitudeBoundary
import Langlands.GroupScheme.Rational.NumberFieldQuaternionicSpinRealBoundary
import Langlands.GroupScheme.Rational.NumberFieldQuaternionicSpinorValue

/-! # The central part of the quaternionic spin Hasse kernel -/

universe u

namespace Langlands.GroupScheme

/-- **The central part of the quaternionic spin Hasse kernel.** Let `q` be a nondegenerate
quadratic form of rank at least four over a central quaternion division algebra over a number
field `F`, with an orthogonal involution. Let `π` be a spin cover of its isometry group.
For a kernel-valued cocycle on a finite Galois cover `Spec L → Spec F`, if its image in the
spin group is trivial after pullback to every completion, that image is a coboundary on
the original cover. -/
theorem numberFieldQuaternionicSpinKernelHasse :
    NumberFieldQuaternionicSpinKernelHasseStatement.{u} :=
  numberFieldQuaternionicSpinKernelHasse_of_boundaries quaternionicSpinKernelMu
    quaternionicSpinLineSimilitudeBoundary numberFieldQuaternionicSpinRealBoundary
    numberFieldQuaternionicSpinorValue

end Langlands.GroupScheme
