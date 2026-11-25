/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # Tensor compatibility of the closed comparison -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed
open Functor.LaxMonoidal
namespace AlgebraicGeometry.ProEtale.CoefficientHomComparison

/-- A braided lax monoidal functor respects the tensor product of internal morphisms.
Source: Stacks 07A4, 0D6D; Step 10 of the constructible coefficient Hom comparison.
Proof: uncurry the equation. The evaluation equation for the closed comparison removes
its components. The braided monoidal tensor-interchange identity replaces the image
of the middle interchange. Naturality of the tensorator then moves the two evaluations
past it, and the two sides coincide by naturality of the middle interchange.
(blueprint: lem-per-coefficient-hom-tensor-compatibility). -/
theorem closed_comparison_tensor
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory C] [BraidedCategory D] [MonoidalClosed C] [MonoidalClosed D]
    (F : C ⥤ D) [F.LaxBraided] (K L P Q : C) :
    μ F ((ihom K).obj L) ((ihom P).obj Q) ≫
        F.map (curry (tensorμ K P ((ihom K).obj L) ((ihom P).obj Q) ≫
          ((ihom.ev K).app L ⊗ₘ (ihom.ev P).app Q))) ≫
        (ihomComparison F (K ⊗ P)).app (L ⊗ Q) ≫
        (pre (μ F K P)).app (F.obj (L ⊗ Q)) =
      ((ihomComparison F K).app L ⊗ₘ
        (ihomComparison F P).app Q) ≫
        curry (tensorμ (F.obj K) (F.obj P) ((ihom (F.obj K)).obj (F.obj L))
          ((ihom (F.obj P)).obj (F.obj Q)) ≫
          ((ihom.ev (F.obj K)).app (F.obj L) ⊗ₘ
            (ihom.ev (F.obj P)).app (F.obj Q))) ≫
        (ihom (F.obj K ⊗ F.obj P)).map (μ F L Q) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, uncurry_pre_app,
    uncurry_eq, ihomComparison_ev]
  rw [uncurry_natural_left, uncurry_natural_right, uncurry_curry]
  rw [whisker_exchange_assoc]
  erw [μ_natural_right_assoc]
  rw [← F.map_comp]
  erw [whiskerLeft_curry_ihom_ev_app]
  rw [F.map_comp]
  rw [← MonoidalCategory.tensorHom_def'_assoc]
  rw [← tensorμ_comp_μ_tensorHom_μ_comp_μ_assoc]
  rw [Category.assoc, ← μ_natural, tensorHom_comp_tensorHom_assoc]
  rw [← ihomComparison_ev F K L, ← ihomComparison_ev F P Q]
  simp only [Functor.id_obj]
  erw [tensorμ_natural_right_assoc]
  simp only [tensorHom_comp_tensorHom_assoc, Functor.comp_obj]

end AlgebraicGeometry.ProEtale.CoefficientHomComparison
