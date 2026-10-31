import Langlands.Algebra.SymmetricPowerLift

/-! # Linear functoriality of the actual symmetric tensor power -/

noncomputable section
universe u
set_option autoImplicit false
open scoped TensorProduct

namespace Langlands.Algebra.SymmetricTensors

variable {R ι : Type u} {M N P : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P]

/-- Apply a linear map to every factor of the actual symmetric tensor quotient. -/
def map (f : M →ₗ[R] N) : Sym[R] ι M →ₗ[R] Sym[R] ι N :=
  lift ((SymmetricPower.tprod R).compLinearMap (fun _ => f)) (by
    intro e x
    exact SymmetricPower.tprod_equiv e (fun i => f (x i)))

@[simp] theorem map_tprod (f : M →ₗ[R] N) (x : ι → M) :
    map f (SymmetricPower.tprod R x) = SymmetricPower.tprod R (fun i => f (x i)) :=
  lift_tprod _ _ _

@[simp] theorem map_id : map (ι := ι) (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  apply linearMap_ext
  intro x
  simp

@[simp] theorem map_comp (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    map (ι := ι) (g.comp f) = (map g).comp (map f) := by
  apply linearMap_ext
  intro x
  simp

end Langlands.Algebra.SymmetricTensors
