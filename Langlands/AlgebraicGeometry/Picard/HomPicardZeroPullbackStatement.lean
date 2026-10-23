import Langlands.AlgebraicGeometry.Picard.HomFamilyPullback

/-! # Geometric Picard-zero preservation by homomorphism pullback -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Actual rigidified pullback along an abelian-scheme homomorphism preserves
the geometric-fibre Picard-zero condition. -/
def HomPicardZeroPullbackStatement : Prop :=
  ∀ (S : Scheme.{u}) (A B : AbelianScheme S) (f : A ⟶ B)
    (T : Over S) (L : RigidifiedFamily B T),
    IsPicardZeroFamily B L →
      IsPicardZeroFamily A ((homFamilyPullback f T).obj L)

end Langlands.AbelianScheme
