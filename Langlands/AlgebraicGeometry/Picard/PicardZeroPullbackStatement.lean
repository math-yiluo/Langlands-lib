import Langlands.AlgebraicGeometry.Picard.RelativePicardZero

/-! # Pullback preservation of the relative geometric Picard-zero condition -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- The actual relative rigidified pullback preserves the geometric-fibre condition. -/
def PicardZeroPullbackStatement : Prop :=
  ∀ (S : Scheme.{u}) (A : AbelianScheme S) (T U : Over S) (h : T ⟶ U)
    (L : RigidifiedFamily A U), IsPicardZeroFamily A L →
      IsPicardZeroFamily A
        ((RigidifiedLineBundle.relativePullback A.X.hom
          (unitSection A) (unitSection_comp A) h).obj L)

end Langlands.AbelianScheme
