/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Torsion kernels and cokernels in functor categories

A natural transformation between functors to an abelian category whose components have kernels
(resp. cokernels) killed by `a : ℤ` has kernel (resp. cokernel) killed by `a`
(`CategoryTheory.Abelian.FunctorCategory.zsmul_kernel_ι_eq_zero_of_app`,
`CategoryTheory.Abelian.FunctorCategory.zsmul_cokernel_π_eq_zero_of_app`).
-/

@[expose] public section

namespace CategoryTheory.Abelian.FunctorCategory

open Limits

variable {J C : Type*} [Category J] [Category C] [Abelian C] {F G : J ⥤ C}

/-- A natural transformation whose components have kernels killed by `a` has kernel killed
by `a`. -/
theorem zsmul_kernel_ι_eq_zero_of_app (φ : F ⟶ G) {a : ℤ}
    (ha : ∀ j, a • kernel.ι (φ.app j) = 0) : a • kernel.ι φ = 0 := by
  ext j
  have h : (kernel.ι φ).app j ≫ φ.app j = 0 := by
    rw [← NatTrans.comp_app, kernel.condition, NatTrans.app_zero]
  rw [NatTrans.app_zsmul, NatTrans.app_zero, ← kernel.lift_ι (φ.app j) _ h,
    ← Preadditive.comp_zsmul, ha, comp_zero]

/-- A natural transformation whose components have cokernels killed by `b` has cokernel killed
by `b`. -/
theorem zsmul_cokernel_π_eq_zero_of_app (φ : F ⟶ G) {b : ℤ}
    (hb : ∀ j, b • cokernel.π (φ.app j) = 0) : b • cokernel.π φ = 0 := by
  ext j
  have h : φ.app j ≫ (cokernel.π φ).app j = 0 := by
    rw [← NatTrans.comp_app, cokernel.condition, NatTrans.app_zero]
  rw [NatTrans.app_zsmul, NatTrans.app_zero, ← cokernel.π_desc (φ.app j) _ h,
    ← Preadditive.zsmul_comp, hb, zero_comp]

end CategoryTheory.Abelian.FunctorCategory
