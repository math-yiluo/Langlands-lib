import Langlands.GroupScheme.Cohomology.RegularCochains
import Langlands.GroupScheme.Torus.RelativeMultiplicativeType

/-! # Statement: regular low-degree cohomology vanishes for multiplicative type -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme.Cohomology

/-- The degree-one and degree-two cases of positive Hochschild cohomology
vanishing for multiplicative-type groups over an affine base
(Conrad, Appendix B.2, Remark B.2.4), in regular affine-test cochain form. -/
def MultiplicativeTypeLowDegreeVanishingStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (H : GroupScheme (Spec R)),
    RelativeMultiplicativeType.IsMultiplicativeType H →
      HasVanishingLowDegreeCohomology H

end Langlands.GroupScheme.Cohomology
