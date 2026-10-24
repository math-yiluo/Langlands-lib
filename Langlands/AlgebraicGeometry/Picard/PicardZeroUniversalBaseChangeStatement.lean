import Langlands.AlgebraicGeometry.Picard.PoincareBaseChange

/-! # Base change of the actual Picard-zero universal property -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- An actual universal Picard-zero family remains universal after the explicit
simultaneous change of its parameter scheme and ground base. -/
def PicardZeroUniversalBaseChangeStatement : Prop :=
  ∀ (S S' : Scheme.{u}) (b : S' ⟶ S) (A : AbelianScheme S) (P : Over S)
    (L : RigidifiedFamily A P), IsUniversalPicardZero A L →
      IsUniversalPicardZero ((baseChange b).obj A) ((baseChangeFamily b A P).obj L)

end Langlands.AbelianScheme
