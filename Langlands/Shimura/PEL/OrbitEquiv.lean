import Langlands.Shimura.PEL.OrbitTransport

/-! # Equivalences of right orbit sets -/

namespace Langlands.Shimura.PEL.RightOrbit
variable {G X Y : Type*} [Group G] [MulAction Gᵐᵒᵖ X] [MulAction Gᵐᵒᵖ Y]

/-- A right-equivariant equivalence induces an equivalence of right orbit sets. -/
def equiv (U : Subgroup G) (e : X ≃ Y)
    (he : ∀ x (g : G), e (right x g) = right (e x) g) :
    RightOrbit X U ≃ RightOrbit Y U where
  toFun := map U e he
  invFun := map U e.symm (fun y g => by
    apply e.injective
    simp only [Equiv.apply_symm_apply, he])
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h x => exact congrArg (mk U) (e.symm_apply_apply x)
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h y => exact congrArg (mk U) (e.apply_symm_apply y)

@[simp] theorem equiv_mk (U : Subgroup G) (e : X ≃ Y)
    (he : ∀ x (g : G), e (right x g) = right (e x) g) (x : X) :
    equiv U e he (mk U x) = mk U (e x) := rfl

@[simp] theorem equiv_symm_mk (U : Subgroup G) (e : X ≃ Y)
    (he : ∀ x (g : G), e (right x g) = right (e x) g) (y : Y) :
    (equiv U e he).symm (mk U y) = mk U (e.symm y) := rfl
end Langlands.Shimura.PEL.RightOrbit
