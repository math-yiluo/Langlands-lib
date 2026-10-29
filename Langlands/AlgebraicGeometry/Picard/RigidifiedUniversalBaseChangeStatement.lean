import Langlands.AlgebraicGeometry.Picard.PoincareBaseChange
import Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalBundle

/-! # Base change of the actual full rigidified universal property -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- An actual universal rigidified family remains universal for all rigidified families after
the explicit simultaneous change of its parameter scheme and ground base. -/
def RigidifiedUniversalBaseChangeStatement : Prop :=
  ∀ (S S' : Scheme.{u}) (b : S' ⟶ S) (A : AbelianScheme S) (P : Over S)
    (L : RigidifiedFamily A P),
    RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L →
      RigidifiedLineBundle.IsUniversal ((baseChange b).obj A).X.hom
        (unitSection ((baseChange b).obj A)) (unitSection_comp _)
        ((baseChangeFamily b A P).obj L)

end Langlands.AbelianScheme
