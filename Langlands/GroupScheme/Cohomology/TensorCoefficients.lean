import Langlands.GroupScheme.Cohomology.RegularCochains
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Tensoring regular module representations with arbitrary coefficients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cohomology

variable {R : CommRingCat.{u}}
variable (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Regroup coefficient tensors while retaining linearity over the test algebra. -/
def coefficientTensorAssoc (A : CommAlgCat.{u} R) :
    (ModulePoints M A ⊗[R] N) ≃ₗ[A] ModulePoints (M ⊗[R] N) A :=
  TensorProduct.AlgebraTensorModule.assoc R R A A M N

/-- Pair an extended module point with a constant element of another module. -/
def tensorCoefficientPoint (A : CommAlgCat.{u} R)
    (x : ModulePoints M A) (n : N) : ModulePoints (M ⊗[R] N) A :=
  coefficientTensorAssoc M N A (x ⊗ₜ[R] n)

@[simp]
theorem tensorCoefficientPoint_tmul (A : CommAlgCat.{u} R) (a : A) (m : M) (n : N) :
    tensorCoefficientPoint M N A (a ⊗ₜ[R] m) n = a ⊗ₜ[R] (m ⊗ₜ[R] n) := rfl

theorem tensorCoefficientPoint_naturality {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (x : ModulePoints M A) (n : N) :
    modulePointMap (M ⊗[R] N) f (tensorCoefficientPoint M N A x n) =
      tensorCoefficientPoint M N B (modulePointMap M f x) n := by
  induction x using TensorProduct.inductionOn with
  | tmul a m => rfl
  | add x y hx hy =>
    simp only [tensorCoefficientPoint, TensorProduct.add_tmul, map_add] at hx hy ⊢
    exact congrArg₂ (· + ·) hx hy

/-- Extend an automorphism of the first module tensor factor. -/
def tensorLinearAutHom (A : CommAlgCat.{u} R) :
    (ModulePoints M A ≃ₗ[A] ModulePoints M A) →*
      ((ModulePoints M A ⊗[R] N) ≃ₗ[A] (ModulePoints M A ⊗[R] N)) where
  toFun e := TensorProduct.AlgebraTensorModule.congr e (1 : N ≃ₗ[R] N)
  map_one' := TensorProduct.AlgebraTensorModule.congr_one
  map_mul' e f := by
    simpa only [one_mul] using TensorProduct.AlgebraTensorModule.congr_mul e f
      (1 : N ≃ₗ[R] N) (1 : N ≃ₗ[R] N)

variable {M N} {H : GroupScheme (Spec R)}

/-- The original group acts on the first coefficient factor and trivially on
the second, through the canonical coefficient regrouping. -/
def ModuleRepresentation.tensorAction (ρ : ModuleRepresentation M H)
    (N : Type u) [AddCommGroup N] [Module R N] (A : CommAlgCat.{u} R) :
    H.affinePoints A →*
      (ModulePoints (M ⊗[R] N) A ≃ₗ[A] ModulePoints (M ⊗[R] N) A) where
  toFun h := (coefficientTensorAssoc M N A).symm.trans
    ((tensorLinearAutHom M N A (ρ.action A h)).trans (coefficientTensorAssoc M N A))
  map_one' := by
    apply LinearEquiv.ext
    intro x
    simp only [map_one, LinearEquiv.trans_apply]
    exact (coefficientTensorAssoc M N A).apply_symm_apply x
  map_mul' h k := by
    apply LinearEquiv.ext
    intro x
    simp only [map_mul, LinearEquiv.trans_apply, LinearEquiv.mul_apply,
      LinearEquiv.symm_apply_apply]

theorem ModuleRepresentation.tensorAction_point (ρ : ModuleRepresentation M H)
    (N : Type u) [AddCommGroup N] [Module R N] (A : CommAlgCat.{u} R)
    (h : H.affinePoints A) (x : ModulePoints M A) (n : N) :
    ρ.tensorAction N A h (tensorCoefficientPoint M N A x n) =
      tensorCoefficientPoint M N A (ρ.action A h x) n := by
  change coefficientTensorAssoc M N A
      (TensorProduct.AlgebraTensorModule.congr (ρ.action A h) (1 : N ≃ₗ[R] N)
        ((coefficientTensorAssoc M N A).symm
          (coefficientTensorAssoc M N A (x ⊗ₜ[R] n)))) = _
  rw [LinearEquiv.symm_apply_apply, TensorProduct.AlgebraTensorModule.congr_tmul]
  rfl

/-- Tensor a natural quasi-coherent module representation with an arbitrary
base module carrying the trivial action. -/
def ModuleRepresentation.tensorTrivial (ρ : ModuleRepresentation M H)
    (N : Type u) [AddCommGroup N] [Module R N] :
    ModuleRepresentation (M ⊗[R] N) H where
  action A := ρ.tensorAction N A
  naturality {A B} f h x := by
    induction x using TensorProduct.inductionOn with
    | tmul a y =>
      induction y using TensorProduct.inductionOn with
      | tmul m n =>
        change modulePointMap (M ⊗[R] N) f
            (ρ.tensorAction N A h (tensorCoefficientPoint M N A (a ⊗ₜ[R] m) n)) =
          ρ.tensorAction N B (H.affinePointMap f h)
            (modulePointMap (M ⊗[R] N) f
              (tensorCoefficientPoint M N A (a ⊗ₜ[R] m) n))
        rw [ModuleRepresentation.tensorAction_point, tensorCoefficientPoint_naturality,
          tensorCoefficientPoint_naturality, ModuleRepresentation.tensorAction_point,
          ρ.naturality]
      | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
    | add x y hx hy => simp only [map_add, hx, hy]

end Langlands.GroupScheme.Cohomology
