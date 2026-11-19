import Langlands.RingTheory.Grassmannian.BaseChangeMembership
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Faithful comparison of stabilized quotient kernels -/

noncomputable section
universe u
set_option autoImplicit false
open scoped TensorProduct

namespace Langlands.Grassmannian

open TensorProduct Module.Grassmannian.PrincipalDescent

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)

/-- Actual extension of coefficients is injective on any tensor module under
faithfully flat coefficient extension. -/
theorem rTensor_eq_zero_iff (hφ : letI : Algebra A B := φ.toAlgebra; Module.FaithfullyFlat A B)
    {E : Type u} [AddCommGroup E] [Module R E] (z : A ⊗[R] E) :
    φ.toLinearMap.rTensor E z = 0 ↔ z = 0 := by
  let : Algebra A B := φ.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' (φ.comp_algebraMap).symm
  let : Module.FaithfullyFlat A B := hφ
  rw [← l_eq_rTensor]
  have hh : AlgebraTensorModule.cancelBaseChange R A B B E ((1 : B) ⊗ₜ[A] z) =
      l R E A B z := by
    rw [cancelBaseChange_tmul_eq_smul_l, one_smul]
  rw [← hh, (AlgebraTensorModule.cancelBaseChange R A B B E).map_eq_zero_iff]
  exact Module.FaithfullyFlat.one_tmul_eq_zero_iff A (A ⊗[R] E) z

/-- Membership in a classified quotient kernel is reflected by faithfully flat
coefficient extension using the actual tensor coefficient map. -/
theorem mem_map_iff (hφ : letI : Algebra A B := φ.toAlgebra; Module.FaithfullyFlat A B)
    {E : Type u} [AddCommGroup E] [Module R E] {k : ℕ}
    (N : Module.Grassmannian A (A ⊗[R] E) k) (z : A ⊗[R] E) :
    φ.toLinearMap.rTensor E z ∈ (Module.Grassmannian.map φ N).toSubmodule ↔
      z ∈ N.toSubmodule := by
  let : Algebra A B := φ.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' (φ.comp_algebraMap).symm
  let : Module.FaithfullyFlat A B := hφ
  rw [map_toSubmodule' R E φ (fun _ => rfl) N, LinearMap.mem_ker,
    ← l_eq_rTensor, baseChangeMkQ_l, Module.FaithfullyFlat.one_tmul_eq_zero_iff,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

variable {E C : Type u} [AddCommGroup E] [Module R E] [AddCommGroup C] [Module R C]

/-- The product-stabilized kernel of an actual first-factor linear map. -/
def productKernel {P : Type u} [AddCommGroup P] [Module A P] (T : A ⊗[R] E →ₗ[A] P) :
    Submodule A (A ⊗[R] (E × C)) :=
  (T.ker.prod (⊥ : Submodule A (A ⊗[R] C))).comap
    (TensorProduct.prodRight R A A E C).toLinearMap

/-- Splitting a tensor product with a product commutes with actual coefficient pullback. -/
theorem prodRight_rTensor (z : A ⊗[R] (E × C)) :
    TensorProduct.prodRight R B B E C (φ.toLinearMap.rTensor (E × C) z) =
      (φ.toLinearMap.rTensor E ((TensorProduct.prodRight R A A E C) z).1,
        φ.toLinearMap.rTensor C ((TensorProduct.prodRight R A A E C) z).2) := by
  induction z using TensorProduct.inductionOn with
  | tmul a ec => rfl
  | add x y hx hy => simp only [map_add, hx, hy, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]

/-- A faithfully flat lifted product-kernel comparison descends to the actual
first-factor kernel stabilized by zero. -/
theorem productKernel_eq_classified
    (hφ : letI : Algebra A B := φ.toAlgebra; Module.FaithfullyFlat A B)
    {P Q : Type u} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module B Q]
    (T : A ⊗[R] E →ₗ[A] P) (L : B ⊗[R] E →ₗ[B] Q) {k : ℕ}
    (N : Module.Grassmannian A (A ⊗[R] (E × C)) k)
    (hN : (Module.Grassmannian.map φ N).toSubmodule =
      (L.prodMap (LinearMap.id : B ⊗[R] C →ₗ[B] B ⊗[R] C)).ker.comap
        (TensorProduct.prodRight R B B E C).toLinearMap)
    (hT : ∀ z : A ⊗[R] E, T z = 0 ↔ L (φ.toLinearMap.rTensor E z) = 0) :
    productKernel (C := C) T = N.toSubmodule := by
  ext z
  rw [← mem_map_iff φ hφ N z, hN]
  change (T ((TensorProduct.prodRight R A A E C) z).1 = 0 ∧
    ((TensorProduct.prodRight R A A E C) z).2 = 0) ↔ _
  rw [Submodule.mem_comap, LinearMap.mem_ker]
  change _ ↔ (L.prodMap (LinearMap.id : B ⊗[R] C →ₗ[B] B ⊗[R] C))
    (TensorProduct.prodRight R B B E C (φ.toLinearMap.rTensor (E × C) z)) = 0
  rw [prodRight_rTensor, LinearMap.prodMap_apply, LinearMap.id_apply, Prod.mk_eq_zero,
    ← hT, rTensor_eq_zero_iff φ hφ]

end Langlands.Grassmannian
