/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Scalar transport of normalized unit counits

The categorical calculation in Step 5 of open-immersion purity normalization.
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory

namespace AlgebraicGeometry.ProEtale.NormalizedUnitTrace

/-- The pointwise scalar counit calculation also applies when the adjunctions
are restricted to full subcategories but the scalar functors remain ambient. -/
theorem scalarUnitTraceTransport_pointwise
    {C₀ D₀ C₁ D₁ : Type*}
    [Category C₀] [Category D₀] [Category C₁] [Category D₁]
    (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁) (H₁ : D₁ ⥤ C₁)
    (S : C₀ ⥤ C₁) (T : D₀ ⥤ D₁) (b : F₀ ⋙ T ⟶ S ⋙ F₁)
    {U₀ : D₀} {U₁ : D₁} (u : T.obj U₀ ≅ U₁)
    {L₀ M₀ : C₀} {M₁ : C₁} (v₀ : L₀ ≅ M₀) (v₁ : H₁.obj U₁ ≅ M₁)
    (c : S.obj L₀ ≅ H₁.obj (T.obj U₀))
    (e₀ : F₀.obj L₀ ⟶ U₀)
    (e₁ : F₁.obj (H₁.obj (T.obj U₀)) ⟶ T.obj U₀)
    (e₁' : F₁.obj (H₁.obj U₁) ⟶ U₁)
    [IsIso (b.app M₀)]
    (hscalar : T.map e₀ = b.app L₀ ≫ F₁.map c.hom ≫ e₁)
    (hnat : F₁.map (H₁.map u.inv) ≫ e₁ = e₁' ≫ u.inv) :
    F₁.map v₁.inv ≫ e₁' =
      F₁.map ((v₁.symm ≪≫ H₁.mapIso u.symm ≪≫ c.symm ≪≫ S.mapIso v₀).hom) ≫
        inv (b.app M₀) ≫ T.map (F₀.map v₀.inv ≫ e₀) ≫ u.hom := by
  let w := v₁.symm ≪≫ H₁.mapIso u.symm ≪≫ c.symm ≪≫ S.mapIso v₀
  have hb : T.map (F₀.map v₀.inv) ≫ b.app L₀ =
      b.app M₀ ≫ F₁.map (S.map v₀.inv) := b.naturality v₀.inv
  have hw : w.hom ≫ S.map v₀.inv ≫ c.hom = v₁.inv ≫ H₁.map u.inv := by
    simp [w, Category.assoc]
  symm
  change F₁.map w.hom ≫ inv (b.app M₀) ≫ T.map (F₀.map v₀.inv ≫ e₀) ≫ u.hom = _
  calc
    _ = F₁.map w.hom ≫ inv (b.app M₀) ≫
        (T.map (F₀.map v₀.inv) ≫ b.app L₀) ≫ F₁.map c.hom ≫ e₁ ≫ u.hom := by
      rw [T.map_comp, hscalar]
      simp only [Category.assoc]
    _ = F₁.map w.hom ≫ F₁.map (S.map v₀.inv) ≫ F₁.map c.hom ≫ e₁ ≫ u.hom := by
      rw [hb]
      simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    _ = F₁.map (v₁.inv ≫ H₁.map u.inv) ≫ e₁ ≫ u.hom := by
      rw [← F₁.map_comp_assoc, ← F₁.map_comp_assoc, Category.assoc, hw]
    _ = F₁.map v₁.inv ≫ e₁' := by
      simp only [F₁.map_comp, Category.assoc]
      rw [← Category.assoc (F₁.map (H₁.map u.inv)) e₁ u.hom, hnat]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Transport a smooth counit through its specified scalar square and the unit
and Tate-line identifications. The formula retains all three comparison maps. -/
theorem scalarUnitTraceTransport
    {C₀ D₀ C₁ D₁ : Type*}
    [Category C₀] [Category D₀] [Category C₁] [Category D₁]
    {F₀ : C₀ ⥤ D₀} {H₀ : D₀ ⥤ C₀} (a₀ : F₀ ⊣ H₀)
    {F₁ : C₁ ⥤ D₁} {H₁ : D₁ ⥤ C₁} (a₁ : F₁ ⊣ H₁)
    (S : C₀ ⥤ C₁) (T : D₀ ⥤ D₁)
    (b : F₀ ⋙ T ≅ S ⋙ F₁) (c : H₀ ⋙ S ≅ T ⋙ H₁)
    {U₀ : D₀} {U₁ : D₁} (u : T.obj U₀ ≅ U₁)
    {M₀ : C₀} {M₁ : C₁} (v₀ : H₀.obj U₀ ≅ M₀) (v₁ : H₁.obj U₁ ≅ M₁)
    (h : T.map (a₀.counit.app U₀) = b.hom.app (H₀.obj U₀) ≫
      F₁.map (c.hom.app U₀) ≫ a₁.counit.app (T.obj U₀)) :
    F₁.map v₁.inv ≫ a₁.counit.app U₁ =
      F₁.map ((v₁.symm ≪≫ H₁.mapIso u.symm ≪≫ (c.app U₀).symm ≪≫
        S.mapIso v₀).hom) ≫ b.inv.app M₀ ≫
          T.map (F₀.map v₀.inv ≫ a₀.counit.app U₀) ≫ u.hom := by
  let w := v₁.symm ≪≫ H₁.mapIso u.symm ≪≫ (c.app U₀).symm ≪≫ S.mapIso v₀
  have hb : b.inv.app M₀ ≫ T.map (F₀.map v₀.inv) =
      F₁.map (S.map v₀.inv) ≫ b.inv.app (H₀.obj U₀) :=
    (b.inv.naturality v₀.inv).symm
  have he : b.inv.app (H₀.obj U₀) ≫ T.map (a₀.counit.app U₀) =
      F₁.map (c.hom.app U₀) ≫ a₁.counit.app (T.obj U₀) := by
    rw [h]
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  have hw : w.hom ≫ S.map v₀.inv ≫ c.hom.app U₀ =
      v₁.inv ≫ H₁.map u.inv := by
    simp [w, Category.assoc]
  symm
  change F₁.map w.hom ≫ b.inv.app M₀ ≫
    T.map (F₀.map v₀.inv ≫ a₀.counit.app U₀) ≫ u.hom = _
  calc
    _ = F₁.map w.hom ≫ (b.inv.app M₀ ≫ T.map (F₀.map v₀.inv)) ≫
        T.map (a₀.counit.app U₀) ≫ u.hom := by
      simp only [Functor.map_comp, Category.assoc]
    _ = F₁.map (w.hom ≫ S.map v₀.inv) ≫
        (b.inv.app (H₀.obj U₀) ≫ T.map (a₀.counit.app U₀)) ≫ u.hom := by
      rw [hb]
      simp only [Functor.map_comp, Category.assoc]
    _ = F₁.map (w.hom ≫ S.map v₀.inv ≫ c.hom.app U₀) ≫
        a₁.counit.app (T.obj U₀) ≫ u.hom := by
      rw [he]
      simp only [Functor.map_comp, Category.assoc]
    _ = F₁.map v₁.inv ≫ (F₁.map (H₁.map u.inv) ≫
        a₁.counit.app (T.obj U₀)) ≫ u.hom := by
      rw [hw]
      simp only [Functor.map_comp, Category.assoc]
    _ = F₁.map v₁.inv ≫ a₁.counit.app U₁ := by
      have hn := a₁.counit.naturality u.inv
      change F₁.map (H₁.map u.inv) ≫ a₁.counit.app (T.obj U₀) =
        a₁.counit.app U₁ ≫ u.inv at hn
      rw [hn]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.ProEtale.NormalizedUnitTrace
