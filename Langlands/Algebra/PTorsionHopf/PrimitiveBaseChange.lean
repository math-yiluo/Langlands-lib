import Mathlib.RingTheory.Bialgebra.TensorProduct
import Mathlib.RingTheory.Bialgebra.Primitive

/-! # Primitive defects and scalar extension -/

noncomputable section

open Coalgebra TensorProduct

namespace Langlands.Algebra.PTorsionHopf

variable (k : Type*) [CommRing k] (A : Type*) [CommRing A] [Bialgebra k A]

/-- The linear defect of primitivity. -/
def primitiveDefect : A →ₗ[k] A ⊗[k] A :=
  comul - TensorProduct.mk k A A 1 - (TensorProduct.mk k A A).flip 1

@[simp] theorem primitiveDefect_apply (a : A) :
    primitiveDefect k A a = comul a - 1 ⊗ₜ[k] a - a ⊗ₜ[k] 1 := rfl

@[simp] theorem mem_ker_primitiveDefect (a : A) :
    a ∈ LinearMap.ker (primitiveDefect k A) ↔ Bialgebra.IsPrimitiveElem k a := by
  rw [LinearMap.mem_ker, primitiveDefect_apply,
    Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul, sub_sub, sub_eq_zero]

variable (L : Type*) [CommRing L] [Algebra k L]

/-- The tensor comparison for the target of scalar-extended comultiplication. -/
def primitiveTensorComparison :
    L ⊗[k] (A ⊗[k] A) ≃ₗ[L] (L ⊗[k] A) ⊗[L] (L ⊗[k] A) :=
  AlgebraTensorModule.congr (TensorProduct.lid L L).symm (LinearEquiv.refl k (A ⊗[k] A)) ≪≫ₗ
    AlgebraTensorModule.tensorTensorTensorComm k L k L L L A A

@[simp] theorem primitiveTensorComparison_tmul (l : L) (a b : A) :
    primitiveTensorComparison k A L (l ⊗ₜ[k] (a ⊗ₜ[k] b)) =
      (1 ⊗ₜ[k] a) ⊗ₜ[L] (l ⊗ₜ[k] b) := rfl

/-- Under the canonical tensor comparison, the scalar extension of the
primitive defect is exactly the primitive defect after scalar extension. -/
theorem primitiveTensorComparison_comp_defect :
    (primitiveTensorComparison k A L).toLinearMap ∘ₗ
      (primitiveDefect k A).baseChange L = primitiveDefect L (L ⊗[k] A) := by
  apply LinearMap.restrictScalars_injective k
  apply TensorProduct.ext'
  intro l a
  change primitiveTensorComparison k A L (l ⊗ₜ[k] primitiveDefect k A a) =
    primitiveDefect L (L ⊗[k] A) (l ⊗ₜ[k] a)
  simp only [primitiveDefect_apply, TensorProduct.tmul_sub, map_sub,
    primitiveTensorComparison_tmul]
  have hcomul : primitiveTensorComparison k A L (l ⊗ₜ[k] comul a) =
      comul (R := L) (l ⊗ₜ[k] a) := rfl
  rw [hcomul]
  congr 1
  rw [Algebra.TensorProduct.one_def]
  simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
    (TensorProduct.tmul_smul (R := L) l ((1 : L) ⊗ₜ[k] a)
      ((1 : L) ⊗ₜ[k] (1 : A)))

/-- Primitives after scalar extension are the kernel of the scalar-extended
primitive defect. -/
theorem mem_ker_baseChange_primitiveDefect (x : L ⊗[k] A) :
    x ∈ LinearMap.ker ((primitiveDefect k A).baseChange L) ↔
      Bialgebra.IsPrimitiveElem L x := by
  rw [← mem_ker_primitiveDefect L (L ⊗[k] A), LinearMap.mem_ker, LinearMap.mem_ker]
  have h := LinearMap.congr_fun (primitiveTensorComparison_comp_defect k A L) x
  change primitiveTensorComparison k A L ((primitiveDefect k A).baseChange L x) =
    primitiveDefect L (L ⊗[k] A) x at h
  rw [← h, (primitiveTensorComparison k A L).map_eq_zero_iff]

end Langlands.Algebra.PTorsionHopf
