import Langlands.GroupScheme.Torus.RelativeMultiplicativeType

/-! # Statement: flat nilpotent deformations of multiplicative-type groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open RelativeMultiplicativeType in
/-- A flat group scheme over an affine base is of multiplicative type if its reduction
modulo a nilpotent ideal is of multiplicative type (SGA 3, X, Corollary 2.3). -/
def MultiplicativeTypeFlatNilpotentReflectionStatement : Prop :=
  ∀ (A : Type u) [CommRing A] (J : Ideal A), IsNilpotent J →
    ∀ H : GroupScheme (Spec (CommRingCat.of A)), Flat H.X.hom →
      IsMultiplicativeType ((GroupScheme.baseChange (Spec.algebraMap A (A ⧸ J))).obj H) →
        IsMultiplicativeType H

end Langlands.GroupScheme
