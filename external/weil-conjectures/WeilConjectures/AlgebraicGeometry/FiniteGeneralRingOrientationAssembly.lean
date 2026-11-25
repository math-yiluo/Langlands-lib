/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
/-! Categorical pasting for coefficient orientations.
(blueprint: lem-sp-general-ring-orientation-assembly). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- Naturality of an adjunction unit under the right mate of an isomorphism.
Source: coefficient comparison of site adjunctions
(blueprint: lem-sp-general-ring-orientation-assembly). -/
private theorem scalarOriginUnit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    (a : F ⊣ G) (b : F' ⊣ G') (S : C ⥤ C') (T : D ⥤ D')
    (e : F ⋙ T ≅ S ⋙ F') (M : C) :
    S.map (a.unit.app M) ≫
        b.homEquiv _ _ (e.inv.app (G.obj (F.obj M)) ≫ T.map (a.counit.app (F.obj M))) =
      b.unit.app (S.obj M) ≫ G'.map (e.inv.app M) := by
  rw [Adjunction.homEquiv_unit]
  have hu := b.unit.naturality (S.map (a.unit.app M))
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hu
  dsimp only [Functor.comp_obj]
  rw [reassoc_of% hu, ← G'.map_comp]
  have hn := e.inv.naturality (a.unit.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  have hc : F'.map (S.map (a.unit.app M)) ≫
      (e.inv.app (G.obj (F.obj M)) ≫ T.map (a.counit.app (F.obj M))) =
      e.inv.app M := by
    rw [← Category.assoc, hn, Category.assoc, ← T.map_comp,
      a.left_triangle_components, T.map_id, Category.comp_id]
  rw [hc]

private theorem scalarOriginUnit_comp
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
    (a : F ⊣ G) (b : F' ⊣ G') (S : C ⥤ C') (T : D ⥤ D')
    (e : F ⋙ T ≅ S ⋙ F') (M : C) (M' : C')
    (v : S.obj M ⟶ M') (w : T.obj (F.obj M) ⟶ F'.obj M')
    (hw : w = e.hom.app M ≫ F'.map v) :
    S.map (a.unit.app M) ≫
      b.homEquiv _ _ (e.inv.app (G.obj (F.obj M)) ≫ T.map (a.counit.app (F.obj M))) ≫
      G'.map w = v ≫ b.unit.app M' := by
  rw [← Category.assoc, scalarOriginUnit, Category.assoc, hw, ← G'.map_comp]
  simp only [Iso.inv_hom_id_app_assoc]
  have h := b.unit.naturality v
  dsimp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at h
  exact h.symm

/-- Paste the scalar square with the two orientation isomorphisms.
Source: general-ring purity, pasting of the three squares
(blueprint: lem-sp-general-ring-orientation-assembly). -/
theorem assembleOrientation
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (F : C ⥤ D) (F' : C' ⥤ D') (S : D ⥤ D') (T : C ⥤ C')
    (q : F ⋙ S ≅ T ⋙ F') {M L : C} {M' L' : C'} {W : D} {W' : D'}
    (u : F.obj M ≅ W) (u' : F'.obj M' ≅ W') (a : M ≅ L) (a' : M' ≅ L')
    (v : W ≅ F.obj L) (t : T.obj L ≅ L')
    (c : T.obj M ⟶ M') [IsIso c] (r : S.obj W ⟶ W')
    (hv : u.hom ≫ v.hom = F.map a.hom)
    (hc : c ≫ a'.hom = T.map a.hom ≫ t.hom)
    (hr : S.map u.hom ≫ r = q.hom.app M ≫ F'.map c ≫ u'.hom) :
    IsIso r ∧ r ≫ u'.inv ≫ F'.map a'.hom =
      S.map v.hom ≫ q.hom.app L ≫ F'.map t.hom := by
  have hformula : r = inv (S.map u.hom) ≫ q.hom.app M ≫ F'.map c ≫ u'.hom := by
    apply (cancel_epi (S.map u.hom)).1
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using hr
  refine ⟨by rw [hformula]; infer_instance, ?_⟩
  apply (cancel_epi (S.map u.hom)).1
  rw [← Category.assoc, hr]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← F'.map_comp, hc, F'.map_comp]
  rw [← S.map_comp_assoc, hv]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun z ↦ z ≫ F'.map t.hom) (q.hom.naturality a.hom).symm

end AlgebraicGeometry.ProEtale
