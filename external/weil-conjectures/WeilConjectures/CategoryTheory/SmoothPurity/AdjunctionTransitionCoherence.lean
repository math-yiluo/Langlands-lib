/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

/-! # Transition coherence from a right-adjoint cocone

Source: the horizontal composition law for adjunction mates, Stacks 0FND.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory
variable {X Y A B C D : Type*}
  [Category X] [Category Y] [Category A] [Category B] [Category C] [Category D]
  {F : X ⥤ Y} {U : Y ⥤ X}
  {Ga : X ⥤ A} {Gb : X ⥤ B}
  {Va : Y ⥤ A} {Vb : Y ⥤ B} {Vm : Y ⥤ C} {Vn : Y ⥤ D}
  {Lp : A ⥤ C} {Rp : C ⥤ A} {Lq : B ⥤ D} {Rq : D ⥤ B}
  {Lh : D ⥤ C} {Rh : C ⥤ D} {Lk : B ⥤ A} {Rk : A ⥤ B}
  {Lt : B ⥤ C} {Rt : C ⥤ B}

/-- Tensor-adjoint transitions in an evaluated left extension are determined by
composition of the right cocone. Source: Stacks 0FND
(blueprint: lem-pur-adjunction-transition-coherence).
Proof: precompose with the inverse upper evaluation comparison and the inverse first
associator. Transpose both sides to the total scalar adjunction. The composite
transpose formula replaces the associators by restriction compositors. The two
evaluation transpose equations reduce the result to the right cocone composition
law and naturality of the original transition with respect to the extension unit.
Invertibility of the two precomposing maps gives the desired equation. -/
theorem adjunctionTransition_coherence
    (a : F ⊣ U) (ap : Lp ⊣ Rp) (aq : Lq ⊣ Rq) (ah : Lh ⊣ Rh)
    (ak : Lk ⊣ Rk) (ac : Lt ⊣ Rt)
    (δ₁ : Rh ⋙ Rq ≅ Rt) (δ₂ : Rp ⋙ Rk ≅ Rt)
    (γa : U ⋙ Ga ⟶ Va) (γb : U ⋙ Gb ⟶ Vb)
    (τk : Gb ⟶ Ga ⋙ Rk) (τh : Vn ⟶ Vm ⋙ Rh)
    (τp : Va ⟶ Vm ⋙ Rp) (τq : Vb ⟶ Vn ⋙ Rq)
    (νa : F ⋙ Vm ≅ Ga ⋙ Lp) (νb : F ⋙ Vn ≅ Gb ⋙ Lq)
    (hνa : ∀ N, ap.homEquiv _ _ (νa.inv.app N) =
      Ga.map (a.unit.app N) ≫ γa.app (F.obj N) ≫ τp.app (F.obj N))
    (hνb : ∀ N, aq.homEquiv _ _ (νb.inv.app N) =
      Gb.map (a.unit.app N) ≫ γb.app (F.obj N) ≫ τq.app (F.obj N))
    (hright : ∀ M, γb.app M ≫ τq.app M ≫ Rq.map (τh.app M) ≫ δ₁.hom.app (Vm.obj M) =
      τk.app (U.obj M) ≫ Rk.map (γa.app M) ≫ Rk.map (τp.app M) ≫
        δ₂.hom.app (Vm.obj M)) (N : X) :
    (ah.homEquiv _ _).symm (τh.app (F.obj N)) =
      Lh.map (νb.hom.app N) ≫
      (((aq.comp ah).ofNatIsoRight δ₁).leftAdjointUniq ac).hom.app (Gb.obj N) ≫
      (((ak.comp ap).ofNatIsoRight δ₂).leftAdjointUniq ac).inv.app (Gb.obj N) ≫
      Lp.map ((ak.homEquiv _ _).symm (τk.app N)) ≫ νa.inv.app N := by
  let e₁ := ((aq.comp ah).ofNatIsoRight δ₁).leftAdjointUniq ac
  let e₂ := ((ak.comp ap).ofNatIsoRight δ₂).leftAdjointUniq ac
  have hc : e₁.inv.app (Gb.obj N) ≫ Lh.map (νb.inv.app N) ≫
      (ah.homEquiv _ _).symm (τh.app (F.obj N)) =
      e₂.inv.app (Gb.obj N) ≫ Lp.map ((ak.homEquiv _ _).symm (τk.app N)) ≫
        νa.inv.app N := by
    apply (ac.homEquiv _ _).injective
    have h₁ := adjunctionComposition_transpose aq ah ac δ₁ (Gb.obj N)
      (Vn.obj (F.obj N)) (Vm.obj (F.obj N))
      (aq.homEquiv _ _ (νb.inv.app N)) (τh.app (F.obj N))
    have h₂ := adjunctionComposition_transpose ak ap ac δ₂ (Gb.obj N)
      (Ga.obj N) (Vm.obj (F.obj N)) (τk.app N) (ap.homEquiv _ _ (νa.inv.app N))
    simp only [Equiv.symm_apply_apply] at h₁ h₂
    erw [h₁, h₂]
    erw [hνa, hνb]
    simp only [Functor.map_comp, Category.assoc]
    rw [hright]
    have hn := τk.naturality (a.unit.app N)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [reassoc_of% hn]
  apply (cancel_epi (Lh.map (νb.inv.app N))).1
  simp only [← Lh.map_comp_assoc, Iso.inv_hom_id_app, Lh.map_id, Category.id_comp]
  apply (cancel_epi (e₁.inv.app (Gb.obj N))).1
  rw [Iso.inv_hom_id_app_assoc]
  exact hc

end CategoryTheory
