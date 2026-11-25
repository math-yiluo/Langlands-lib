/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Cancellation for a mixed tensor comparison

Source: Stacks Project, sites-cohomology.tex, Tag 07A4, mixed tensor comparison.
The forward counit square is multiplied by the inverses of its two horizontal
isomorphisms. Naturality moves the comparison between functors past the tensorator.
The first tensor factor then cancels its inverse, leaving the mixed counit.
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory MonoidalCategory

namespace CategoryTheory

/-- Naturality and cancellation convert a forward tensor counit square into its mixed
inverse square. No tensorator or counit is assumed invertible.

Proof. Postcompose both sides with `c.hom`, use naturality of `κ` on `m`, and replace
`L.map m ≫ κ_T ≫ aT ≫ c.hom` by the forward square. Cancel `φ.inv ≫ φ.hom`, then use
functoriality of tensor to cancel `κ_P.inv ≫ κ_P.hom` in its first factor.
(blueprint: lem-sf-finite-open-mixed-tensor-representative-inverse-transport) -/
theorem mixedTensor_inverse_transport
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (L R : C ⥤ D) (κ : L ≅ R) {P Q T : C} {EP EQ ET V : D}
    (φ : L.obj (P ⊗ Q) ≅ L.obj P ⊗ L.obj Q)
    (m : P ⊗ Q ⟶ T) (aP : R.obj P ⟶ EP) (aQ : R.obj Q ⟶ EQ)
    (aT : R.obj T ⟶ ET) (t : EP ⊗ EQ ⟶ V) (c : ET ≅ V)
    (h : φ.hom ≫ ((κ.hom.app P ≫ aP) ⊗ₘ (κ.hom.app Q ≫ aQ)) ≫ t =
      L.map m ≫ κ.hom.app T ≫ aT ≫ c.hom) :
    (κ.inv.app P ⊗ₘ 𝟙 (L.obj Q)) ≫ φ.inv ≫ κ.hom.app (P ⊗ Q) ≫ R.map m ≫ aT =
      (aP ⊗ₘ (κ.hom.app Q ≫ aQ)) ≫ t ≫ c.inv := by
  apply (cancel_mono c.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← κ.hom.naturality_assoc m, ← h]
  simp only [Iso.inv_hom_id_assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [Iso.inv_hom_id_app_assoc, Category.id_comp]

end CategoryTheory
