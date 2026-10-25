import Langlands.AlgebraicGeometry.Picard.FamilyBaseChange

/-! # Geometric Picard zero under ground base change -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Actual ground-base pullback preserves and reflects the geometric-fibre
Picard-zero condition on rigidified families. -/
def PicardZeroFamilyBaseChangeStatement : Prop :=
  ∀ (S S' : Scheme.{u}) (b : S' ⟶ S) (A : AbelianScheme S)
    (T : Over S') (L : RigidifiedFamily A ((Over.map b).obj T)),
    IsPicardZeroFamily A L ↔
      IsPicardZeroFamily ((baseChange b).obj A) ((familyBaseChange b A T).obj L)

end Langlands.AbelianScheme
