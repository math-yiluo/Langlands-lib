import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Analysis.Complex.Basic

/-! # Complex extension of a real Lie homomorphism -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Algebra.ComplexLieExtension

variable {L A : Type*} [LieRing L] [LieAlgebra ℝ L]
  [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The complex-linear tensor extension of a real-linear map. -/
def linear (ρ : L →ₗ[ℝ] A) : ℂ ⊗[ℝ] L →ₗ[ℂ] A :=
  TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton ℂ _ ρ)

@[simp]
theorem linear_tmul (ρ : L →ₗ[ℝ] A) (z : ℂ) (X : L) :
    linear ρ (z ⊗ₜ[ℝ] X) = z • ρ X := rfl

/-- Complexification preserves the Lie law into an associative complex algebra. -/
def lie (ρ : L →ₗ⁅ℝ⁆ A) : ℂ ⊗[ℝ] L →ₗ⁅ℂ⁆ A :=
  { linear ρ.toLinearMap with
    map_lie' := by
      intro U V
      change linear ρ.toLinearMap ⁅U, V⁆ =
        linear ρ.toLinearMap U * linear ρ.toLinearMap V -
          linear ρ.toLinearMap V * linear ρ.toLinearMap U
      induction U using TensorProduct.inductionOn with
      | tmul z X =>
        induction V using TensorProduct.inductionOn with
        | tmul w Y =>
          simp only [LieAlgebra.ExtendScalars.bracket_tmul, linear_tmul]
          change (z * w) • ρ ⁅X, Y⁆ =
            (z • ρ X) * (w • ρ Y) - (w • ρ Y) * (z • ρ X)
          have h := ρ.map_lie X Y
          change ρ ⁅X, Y⁆ = ρ X * ρ Y - ρ Y * ρ X at h
          rw [h]
          simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm w z]
          exact smul_sub (z * w) (ρ X * ρ Y) (ρ Y * ρ X)
        | add U V hU hV =>
          rw [LieRing.lie_add]
          simp only [map_add, hU, hV, mul_add, add_mul]
          abel
      | add U V hU hV =>
        simp only [add_lie, map_add, hU, hV, mul_add, add_mul]
        abel }

@[simp]
theorem lie_tmul (ρ : L →ₗ⁅ℝ⁆ A) (z : ℂ) (X : L) :
    lie ρ (z ⊗ₜ[ℝ] X) = z • ρ X := rfl

/-- The genuine universal enveloping extension of the complexified Lie map. -/
def enveloping (ρ : L →ₗ⁅ℝ⁆ A) :
    UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L) →ₐ[ℂ] A :=
  UniversalEnvelopingAlgebra.lift ℂ (lie ρ)

@[simp]
theorem enveloping_generator (ρ : L →ₗ⁅ℝ⁆ A) (Z : ℂ ⊗[ℝ] L) :
    enveloping ρ (UniversalEnvelopingAlgebra.ι ℂ Z) = lie ρ Z :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ (lie ρ) Z

@[simp]
theorem enveloping_real_generator (ρ : L →ₗ⁅ℝ⁆ A) (X : L) :
    enveloping ρ (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) = ρ X := by
  rw [enveloping_generator, lie_tmul, one_smul]

end Langlands.Algebra.ComplexLieExtension
