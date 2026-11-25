/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.CategoryTheory.Monoidal.UnitComparison
public import WeilConjectures.CategoryTheory.SectionProjectionUnit

/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(blueprint: lem-z8-section-projection-unit).

# Projection cancellation along a section

Source: blueprint thm-amb-p1-adjunction.proof.md, contraction along the diagonal section.
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.Adjunction

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] TwoSquare

/-- Compose tensor comparisons and cancel a section compositor. -/
theorem tensor_compatibility_of_composite_section
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (G : D ⥤ C) (H : C ⥤ C)
    (dF : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    (dG : (Functor.postcompose₂.obj G).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj G).obj G).obj (curriedTensor C))
    (dH : (Functor.postcompose₂.obj H).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ C).obj H).obj H).obj (curriedTensor C))
    (c : H ≅ F ⋙ G) (i : H ≅ 𝟭 C) (M N : C)
    (hc : (dH.app M).app N ≫ (c.hom.app M ⊗ₘ c.hom.app N) =
      c.hom.app (M ⊗ N) ≫ G.map ((dF.app M).app N) ≫
        (dG.app (F.obj M)).app (F.obj N))
    (hi : (dH.app M).app N ≫ (i.hom.app M ⊗ₘ i.hom.app N) =
      i.hom.app (M ⊗ N)) :
    G.map ((dF.app M).app N) ≫ (dG.app (F.obj M)).app (F.obj N) ≫
      ((c.symm ≪≫ i).hom.app M ⊗ₘ (c.symm ≪≫ i).hom.app N) =
      (c.symm ≪≫ i).hom.app (M ⊗ N) := by
  apply (cancel_epi (c.hom.app (M ⊗ N))).mp
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← reassoc_of% hc, tensorHom_comp_tensorHom,
    Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]
  exact hi

private theorem projection_conjugate_at
    {C D : Type*} [Category C] [Category D]
    {F F' : D ⥤ C} {G G' : C ⥤ D} (adj : F ⊣ G) (adj' : F' ⊣ G')
    {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D}
    (φ : (Functor.postcompose₂.obj F).obj T_D ⟶
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj T_C)
    (φ' : (Functor.postcompose₂.obj F').obj T_D ⟶
      (((Functor.whiskeringLeft₂ C).obj F').obj F').obj T_C)
    (α : F' ⟶ F) (M : C) (L : D)
    (hα : α.app ((T_D.obj (G.obj M)).obj L) ≫ (φ.app (G.obj M)).app L =
      (φ'.app (G.obj M)).app L ≫
        (T_C.map (α.app (G.obj M))).app (F'.obj L) ≫
        (T_C.obj (F.obj (G.obj M))).map (α.app L)) :
    (T_D.map ((conjugateEquiv adj adj' α).app M)).app L ≫
        ((adj'.rightAdjointProjectionMap φ').app M).app L ≫
        G'.map ((T_C.obj M).map (α.app L)) =
      ((adj.rightAdjointProjectionMap φ).app M).app L ≫
        (conjugateEquiv adj adj' α).app ((T_C.obj M).obj (F.obj L)) := by
  apply (adj'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    adj'.counit_naturality, conjugateEquiv_counit]
  erw [Adjunction.map_rightAdjointProjectionMap_app_app_comp_counit_assoc]
  erw [α.naturality_assoc]
  erw [adj.map_rightAdjointProjectionMap_app_app_comp_counit φ M L]
  have h₁ := NatTrans.congr_app
    (φ'.naturality ((conjugateEquiv adj adj' α).app M)) L
  dsimp at h₁ ⊢
  rw [reassoc_of% h₁, ← NatTrans.comp_app_assoc, ← T_C.map_comp,
    conjugateEquiv_counit, reassoc_of% hα, T_C.map_comp, NatTrans.comp_app]
  erw [(T_C.map (adj.counit.app M)).naturality (α.app L)]
  simp only [Category.assoc]
  rfl

/-- The projection map for two adjunctions, normalized by a section comparison.
Only tensor compatibility at the chosen second coefficient is needed. -/
private theorem section_projection_composite
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {R : D ⥤ C} {G : D ⥤ C} {S : C ⥤ D}
    (adj : F ⊣ R) (adj' : G ⊣ S)
    (dF : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    (dG : (Functor.postcompose₂.obj G).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj G).obj G).obj (curriedTensor C))
    (l : F ⋙ G ≅ 𝟭 C) (M N : C)
    (hl : G.map ((dF.app M).app N) ≫
      (dG.app (F.obj M)).app (F.obj N) ≫
        (l.hom.app M ⊗ₘ l.hom.app N) = l.hom.app (M ⊗ N)) :
    let t := conjugateIsoEquiv (adj.comp adj') Adjunction.id l.symm
    let pF := adj.rightAdjointProjectionMap
      (T_C := (curriedTensor D).flip) (T_D := (curriedTensor C).flip)
      ((flipFunctor _ _ _).map dF)
    let pG := adj'.rightAdjointProjectionMap
      (T_C := (curriedTensor C).flip) (T_D := (curriedTensor D).flip)
      ((flipFunctor _ _ _).map dG)
    M ◁ t.inv.app N ≫ (pF.app (S.obj N)).app M ≫
      R.map ((pG.app N).app (F.obj M)) ≫
      t.hom.app (G.obj (F.obj M) ⊗ N) ≫ l.hom.app M ▷ N = 𝟙 (M ⊗ N) := by
  let d : (Functor.postcompose₂.obj (F ⋙ G)).obj (curriedTensor C).flip ⟶
      (((Functor.whiskeringLeft₂ C).obj (F ⋙ G)).obj (F ⋙ G)).obj
        (curriedTensor C).flip :=
    (flipFunctor _ _ _).map
      ((Functor.postcompose₂.obj G).map dF ≫
        (((Functor.whiskeringLeft₂ C).obj F).obj F).map dG)
  let e : (Functor.postcompose₂.obj (𝟭 C)).obj (curriedTensor C).flip ⟶
      (((Functor.whiskeringLeft₂ C).obj (𝟭 C)).obj (𝟭 C)).obj
        (curriedTensor C).flip := 𝟙 _
  have he (A B : C) :
      ((Adjunction.id.rightAdjointProjectionMap e).app A).app B = 𝟙 (B ⊗ A) := by
    have hh : ((Adjunction.id : 𝟭 C ⊣ 𝟭 C).homEquiv (B ⊗ A) (B ⊗ A))
        (𝟙 (B ⊗ A)) = 𝟙 (B ⊗ A) := Adjunction.homEquiv_id _ _
    simpa [Adjunction.rightAdjointProjectionMap, e] using hh
  have hc := projection_conjugate_at Adjunction.id (adj.comp adj')
    e d l.hom N M (by
      simpa [d, e, tensorHom_def', Category.assoc] using hl.symm)
  dsimp only [Functor.id_map, Functor.id_obj] at hc
  rw [he] at hc
  have hp := adj.rightAdjointProjectionMap_comp adj'
    (T₁ := (curriedTensor D).flip) (S₁ := (curriedTensor C).flip)
    (T_B := (curriedTensor C).flip)
    ((flipFunctor _ _ _).map dF) ((flipFunctor _ _ _).map dG) d
    (fun _ _ ↦ rfl) N M
  rw [hp] at hc
  dsimp only [Functor.flip_obj_obj, Functor.flip_obj_map] at hc
  dsimp only
  have ht : conjugateEquiv Adjunction.id (adj.comp adj') l.hom =
      (conjugateIsoEquiv (adj.comp adj') Adjunction.id l.symm).inv := by
    rfl
  rw [ht] at hc
  have hn := (conjugateIsoEquiv (adj.comp adj') Adjunction.id l.symm).hom.naturality
    (l.hom.app M ▷ N)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  simp only [Functor.comp_obj, Functor.id_obj] at hn
  simp only [Category.assoc] at hc ⊢
  rw [← hn]
  have hc' := congrArg
    (fun f ↦ f ≫ (conjugateIsoEquiv (adj.comp adj') Adjunction.id l.symm).hom.app
      (M ⊗ N)) hc
  simpa only [curriedTensor_obj_obj, curriedTensor_map_app, Functor.comp_map,
    Category.assoc, Category.id_comp, Iso.inv_hom_id_app,
    Functor.flip_map_app, curriedTensor_obj_map, Functor.id_obj] using hc'

/-- Two ordered projection maps along a section cancel against the conjugate
composition comparison and the right unitors.
Source: blueprint thm-amb-p1-adjunction.proof.md, diagonal contraction.
Proof: the projection map of a composite is the composite of the projection maps.
Conjugate its adjunction to the identity using the section isomorphism. Tensor
compatibility identifies its projection with the identity. Naturality of the
conjugate comparison and of the right unitor gives the displayed equation. -/
theorem section_projection_unit
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {R : D ⥤ C} {G : D ⥤ C} {S : C ⥤ D}
    (adj : F ⊣ R) (adj' : G ⊣ S)
    (dF : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    (dG : (Functor.postcompose₂.obj G).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj G).obj G).obj (curriedTensor C))
    (l : F ⋙ G ≅ 𝟭 C) (M : C)
    (hl : G.map ((dF.app M).app (𝟙_ C)) ≫
      (dG.app (F.obj M)).app (F.obj (𝟙_ C)) ≫
        (l.hom.app M ⊗ₘ l.hom.app (𝟙_ C)) = l.hom.app (M ⊗ 𝟙_ C)) :
    let t := conjugateIsoEquiv (adj.comp adj') Adjunction.id l.symm
    let pF := adj.rightAdjointProjectionMap
      (T_C := (curriedTensor D).flip) (T_D := (curriedTensor C).flip)
      ((flipFunctor _ _ _).map dF)
    let pG := adj'.rightAdjointProjectionMap
      (T_C := (curriedTensor C).flip) (T_D := (curriedTensor D).flip)
      ((flipFunctor _ _ _).map dG)
    (ρ_ M).inv ≫ M ◁ t.inv.app (𝟙_ C) ≫ (pF.app (S.obj (𝟙_ C))).app M ≫
      R.map ((pG.app (𝟙_ C)).app (F.obj M) ≫
        S.map (l.hom.app M ▷ (𝟙_ C) ≫ (ρ_ M).hom)) ≫ t.hom.app M = 𝟙 M := by
  have hc := section_projection_composite adj adj' dF dG l M (𝟙_ C) hl
  let t := conjugateIsoEquiv (adj.comp adj') Adjunction.id l.symm
  have hn := t.hom.naturality (l.hom.app M ▷ (𝟙_ C) ≫ (ρ_ M).hom)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.id_obj] at hn
  dsimp only
  rw [R.map_comp]
  simp only [Category.assoc]
  rw [hn]
  have hc' := congrArg (fun f ↦ (ρ_ M).inv ≫ f ≫ (ρ_ M).hom) hc
  simpa only [Category.assoc, Category.id_comp, Iso.inv_hom_id, t, Functor.comp_obj] using hc'

end CategoryTheory.Adjunction
