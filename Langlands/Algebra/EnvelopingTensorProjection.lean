import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Enveloping lifts to a tensor product of associative algebras -/

noncomputable section

universe uR uL uA uB

open scoped TensorProduct

set_option autoImplicit false

namespace Langlands.Algebra.EnvelopingTensor

variable (R : Type uR) [CommRing R]
variable {L : Type uL} [LieRing L] [LieAlgebra R L]
variable {A : Type uA} [Ring A] [Algebra R A]
variable {B : Type uB} [Ring B] [Algebra R B]

local instance tensorProjectionLeftLieRing : LieRing A :=
  LieRing.ofAssociativeRing
local instance tensorProjectionRightLieRing : LieRing B :=
  LieRing.ofAssociativeRing
local instance tensorProjectionTargetLieRing : LieRing (A ⊗[R] B) :=
  LieRing.ofAssociativeRing
local instance tensorProjectionLeftLieAlgebra : LieAlgebra R A :=
  LieAlgebra.ofAssociativeAlgebra
local instance tensorProjectionRightLieAlgebra : LieAlgebra R B :=
  LieAlgebra.ofAssociativeAlgebra
local instance tensorProjectionTargetLieAlgebra : LieAlgebra R (A ⊗[R] B) :=
  LieAlgebra.ofAssociativeAlgebra

/-- Sum the two tensor-factor images of two genuine Lie maps. -/
def sumLieHom (f : L →ₗ⁅R⁆ A) (g : L →ₗ⁅R⁆ B) : L →ₗ⁅R⁆ (A ⊗[R] B) where
  toFun X := f X ⊗ₜ[R] 1 + 1 ⊗ₜ[R] g X
  map_add' X Y := by
    simp only [map_add, TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  map_smul' r X := by
    simp only [map_smul, TensorProduct.smul_tmul', TensorProduct.tmul_smul,
      smul_add, RingHom.id_apply]
  map_lie' := by
    intro X Y
    simp only [LieHom.map_lie, LieRing.of_associative_ring_bracket,
      TensorProduct.sub_tmul, TensorProduct.tmul_sub, add_mul, mul_add,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    abel

@[simp] theorem sumLieHom_apply (f : L →ₗ⁅R⁆ A) (g : L →ₗ⁅R⁆ B) (X : L) :
    sumLieHom R f g X = f X ⊗ₜ[R] 1 + 1 ⊗ₜ[R] g X := rfl

/-- The universal enveloping lift of the actual sum of the two tensor-factor images. -/
def lift (f : L →ₗ⁅R⁆ A) (g : L →ₗ⁅R⁆ B) :
    UniversalEnvelopingAlgebra R L →ₐ[R] (A ⊗[R] B) :=
  UniversalEnvelopingAlgebra.lift R (sumLieHom R f g)

@[simp] theorem lift_generator (f : L →ₗ⁅R⁆ A) (g : L →ₗ⁅R⁆ B) (X : L) :
    lift R f g (UniversalEnvelopingAlgebra.ι R X) =
      f X ⊗ₜ[R] 1 + 1 ⊗ₜ[R] g X :=
  UniversalEnvelopingAlgebra.lift_ι_apply R _ X

end Langlands.Algebra.EnvelopingTensor
