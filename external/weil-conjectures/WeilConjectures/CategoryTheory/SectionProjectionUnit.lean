/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import WeilConjectures.CategoryTheory.Monoidal.UnitComparison

/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# Projection cancellation along a section

Source: blueprint thm-amb-p1-adjunction.proof.md, contraction along the diagonal section.
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.Adjunction

-- `TwoSquare` is already reducible in Mathlib.

/-- The unit law for a tensor-compatible comultiplication forces tensor compatibility
of its counit. This avoids a separate localization calculation for identity pullback. -/
theorem tensor_compatibility_of_unit_law
    {C : Type*} [Category C] [MonoidalCategory C]
    (F : C ⥤ C) (d : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C))
    (c : F ≅ F ⋙ F) (i : F ≅ 𝟭 C)
    (hc : ∀ X Y : C, (d.app X).app Y ≫ (c.hom.app X ⊗ₘ c.hom.app Y) =
      c.hom.app (X ⊗ Y) ≫ F.map ((d.app X).app Y) ≫
        (d.app (F.obj X)).app (F.obj Y))
    (hu : ∀ X : C, c.hom.app X ≫ F.map (i.hom.app X) = 𝟙 _)
    (X Y : C) [IsIso ((d.app X).app Y)] :
    (d.app X).app Y ≫ (i.hom.app X ⊗ₘ i.hom.app Y) = i.hom.app (X ⊗ Y) := by
  have : F.Faithful := Functor.Faithful.of_iso i.symm
  apply F.map_injective
  apply (cancel_epi (c.hom.app (X ⊗ Y))).mp
  apply (cancel_mono ((d.app X).app Y)).mp
  rw [hu, Category.id_comp]
  rw [Functor.map_comp, Category.assoc, Category.assoc]
  have hnat : F.map (i.hom.app X ⊗ₘ i.hom.app Y) ≫ (d.app X).app Y =
      (d.app (F.obj X)).app (F.obj Y) ≫
        (F.map (i.hom.app X) ⊗ₘ F.map (i.hom.app Y)) := by
    have h₁ := NatTrans.congr_app (d.naturality (i.hom.app X)) (F.obj Y)
    have h₂ := (d.app X).naturality (i.hom.app Y)
    change F.map (i.hom.app X ▷ F.obj Y) ≫ (d.app X).app (F.obj Y) =
      (d.app (F.obj X)).app (F.obj Y) ≫ F.map (i.hom.app X) ▷ F.obj (F.obj Y) at h₁
    change F.map (X ◁ i.hom.app Y) ≫ (d.app X).app Y =
      (d.app X).app (F.obj Y) ≫ F.obj X ◁ F.map (i.hom.app Y) at h₂
    simp only [tensorHom_def, F.map_comp, Functor.id_obj]
    rw [Category.assoc, h₂, ← Category.assoc, h₁]
    simp only [Category.assoc]
  rw [hnat, ← reassoc_of% (hc X Y), tensorHom_comp_tensorHom,
    hu, hu, id_tensorHom_id]
  exact Category.comp_id _

/-- A tensor-compatible comparison with identity is compatible with the unit as well. -/
theorem unit_compatibility_of_tensor
    {C : Type*} [Category C] [MonoidalCategory C] (F : C ⥤ C)
    (d : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj (curriedTensor C))
    (i : F ≅ 𝟭 C) (e : F.obj (𝟙_ C) ⟶ 𝟙_ C) [IsIso e]
    [Epi ((d.app (𝟙_ C)).app (𝟙_ C))]
    (ht : (d.app (𝟙_ C)).app (𝟙_ C) ≫
      (i.hom.app (𝟙_ C) ⊗ₘ i.hom.app (𝟙_ C)) = i.hom.app ((𝟙_ C) ⊗ (𝟙_ C)))
    (he : (d.app (𝟙_ C)).app (𝟙_ C) ≫ e ▷ F.obj (𝟙_ C) ≫
      (λ_ (F.obj (𝟙_ C))).hom = F.map (λ_ (𝟙_ C)).hom) :
    e = i.hom.app (𝟙_ C) := by
  have hc := MonoidalCategory.map_hom_comp_eq_of_whiskerRight_comp_leftUnitor F
    (fun X Y ↦ (d.app X).app Y)
    (fun {_ _} f M ↦ NatTrans.congr_app (d.naturality f) M) e he
    (Iso.refl (𝟙_ C)) (Iso.refl (𝟙_ C))
    (λ_ (𝟙_ C)).hom (λ_ (𝟙_ C)).hom (i.app (𝟙_ C))
    (by simp) (by simp) (by
      simp only [Iso.app_hom]
      rw [← tensorHom_def_assoc, ← Category.assoc, ht]
      exact i.hom.naturality (λ_ (𝟙_ C)).hom)
  simpa only [Iso.refl_hom, Functor.map_id, Category.id_comp, Category.comp_id,
    Iso.app_hom] using hc

/-- The flipped projection is the projection conjugated by the tensor braidings. -/
theorem rightAdjointProjectionMap_flip
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
    {F : C ⥤ D} {R : D ⥤ C} (adj : F ⊣ R)
    (d : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    (hd : ∀ X Y : C, F.map (β_ X Y).hom ≫ (d.app Y).app X =
      (d.app X).app Y ≫ (β_ (F.obj X) (F.obj Y)).hom)
    (M : D) (L : C) :
    ((adj.rightAdjointProjectionMap
      (T_C := (curriedTensor D).flip) (T_D := (curriedTensor C).flip)
      ((flipFunctor _ _ _).map d)).app M).app L =
      (β_ L (R.obj M)).hom ≫ ((adj.rightAdjointProjectionMap d).app M).app L ≫
        R.map (β_ M (F.obj L)).hom := by
  apply (adj.homEquiv _ _).symm.injective
  change (adj.homEquiv (L ⊗ R.obj M) (F.obj L ⊗ M)).symm _ =
    (adj.homEquiv (L ⊗ R.obj M) (F.obj L ⊗ M)).symm _
  simp only [Adjunction.homEquiv_counit, F.map_comp, Category.assoc,
    adj.counit_naturality]
  have hf := adj.map_rightAdjointProjectionMap_app_app_comp_counit
    (T_C := (curriedTensor D).flip) (T_D := (curriedTensor C).flip)
    ((flipFunctor _ _ _).map d) M L
  have hp := adj.map_rightAdjointProjectionMap_app_app_comp_counit d M L
  dsimp only [Functor.flip_obj_obj, Functor.flip_map_app] at hf hp
  erw [hf, reassoc_of% hp]
  change (d.app L).app (R.obj M) ≫ F.obj L ◁ adj.counit.app M = _
  rw [← Category.assoc, hd, Category.assoc]
  congr 1
  change F.obj L ◁ adj.counit.app M =
    (β_ (F.obj L) (F.obj (R.obj M))).hom ≫
      (adj.counit.app M ▷ F.obj L) ≫ (β_ M (F.obj L)).hom
  rw [← id_tensorHom, ← tensorHom_id, ← BraidedCategory.braiding_naturality_assoc]
  simp only [id_tensorHom, Functor.id_obj,
    SymmetricCategory.symmetry, Category.comp_id]

/-- Tensor evaluation commutes with a square once its projection and scalar trace do. -/
theorem tensor_evaluation_baseChange_constant
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalCategory C'] [MonoidalCategory D']
    (F : C ⥤ D) (R : D ⥤ C) (F' : C' ⥤ D') (R' : D' ⥤ C')
    (U : C ⥤ C') (V : D ⥤ D') (σ : U ⋙ F' ≅ F ⋙ V)
    (ex : R ⋙ U ⟶ V ⋙ R')
    (p : R ⋙ (curriedTensor C).flip ⟶
      (Functor.postcompose₂.obj R).obj
        ((((Functor.whiskeringLeft₂ D).obj (𝟭 D)).obj F).obj (curriedTensor D).flip))
    (p' : R' ⋙ (curriedTensor C').flip ⟶
      (Functor.postcompose₂.obj R').obj
        ((((Functor.whiskeringLeft₂ D').obj (𝟭 D')).obj F').obj (curriedTensor D').flip))
    (dU : (Functor.postcompose₂.obj U).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ C').obj U).obj U).obj (curriedTensor C'))
    (dV : (Functor.postcompose₂.obj V).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ D').obj V).obj V).obj (curriedTensor D'))
    (O : C) (O' : C') (eU : U.obj O ⟶ O')
    (r : ∀ K : C, K ⊗ O ≅ K) (r' : ∀ K : C', K ⊗ O' ≅ K)
    (L : D) (L' : D') (c : V.obj L ≅ L')
    (τ : R.obj L ⟶ O) (τ' : R'.obj L' ⟶ O')
    (ht : U.map τ ≫ eU = ex.app L ≫ R'.map c.hom ≫ τ')
    (K : C)
    (hp : U.map ((p.app L).app K) ≫ ex.app (F.obj K ⊗ L) ≫
        R'.map ((dV.app (F.obj K)).app L) =
      (dU.app K).app (R.obj L) ≫ U.obj K ◁ ex.app L ≫
        (p'.app (V.obj L)).app (U.obj K) ≫
          R'.map (σ.hom.app K ▷ V.obj L))
    (hu : (dU.app K).app O ≫ U.obj K ◁ eU ≫ (r' (U.obj K)).hom =
      U.map (r K).hom)
    [IsIso ((p.app L).app K)] [IsIso ((p'.app L').app (U.obj K))] :
    U.map (inv ((p.app L).app K) ≫ K ◁ τ ≫ (r K).hom) =
      ex.app (F.obj K ⊗ L) ≫
        R'.map ((dV.app (F.obj K)).app L ≫
          (σ.inv.app K ⊗ₘ c.hom)) ≫
        inv ((p'.app L').app (U.obj K)) ≫ U.obj K ◁ τ' ≫ (r' (U.obj K)).hom := by
  apply (cancel_epi (U.map ((p.app L).app K))).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [← U.map_comp_assoc, IsIso.hom_inv_id, U.map_id, Category.id_comp]
  have hn := NatTrans.congr_app (p'.naturality c.hom) (U.obj K)
  change U.obj K ◁ R'.map c.hom ≫ (p'.app L').app (U.obj K) =
    (p'.app (V.obj L)).app (U.obj K) ≫ R'.map (F'.obj (U.obj K) ◁ c.hom) at hn
  have hσ : (σ.hom.app K ▷ V.obj L) ≫ (σ.inv.app K ⊗ₘ c.hom) =
      F'.obj (U.obj K) ◁ c.hom := by
    rw [tensorHom_def, ← Category.assoc, ← comp_whiskerRight,
      Iso.hom_inv_id_app, id_whiskerRight, Category.id_comp]
    rfl
  calc
    U.map (K ◁ τ) ≫ U.map (r K).hom =
        U.map (K ◁ τ) ≫ (dU.app K).app O ≫
          U.obj K ◁ eU ≫ (r' (U.obj K)).hom := by rw [hu]
    _ = (dU.app K).app (R.obj L) ≫ U.obj K ◁ (U.map τ ≫ eU) ≫
        (r' (U.obj K)).hom := by
      have h := (dU.app K).naturality τ
      change U.map (K ◁ τ) ≫ (dU.app K).app O =
        (dU.app K).app (R.obj L) ≫ U.obj K ◁ U.map τ at h
      rw [reassoc_of% h, whiskerLeft_comp, Category.assoc]
    _ = (dU.app K).app (R.obj L) ≫ U.obj K ◁ ex.app L ≫
        U.obj K ◁ R'.map c.hom ≫ U.obj K ◁ τ' ≫ (r' (U.obj K)).hom := by
      rw [ht]
      simp only [whiskerLeft_comp, Category.assoc]
    _ = (dU.app K).app (R.obj L) ≫ U.obj K ◁ ex.app L ≫
        (p'.app (V.obj L)).app (U.obj K) ≫
        R'.map (F'.obj (U.obj K) ◁ c.hom) ≫
        inv ((p'.app L').app (U.obj K)) ≫
        U.obj K ◁ τ' ≫ (r' (U.obj K)).hom := by
      rw [← reassoc_of% hn, IsIso.hom_inv_id_assoc]
    _ = _ := by
      rw [← hσ, R'.map_comp]
      simp only [Category.assoc]
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ R'.map (σ.inv.app K ⊗ₘ c.hom) ≫
        inv ((p'.app L').app (U.obj K)) ≫
          U.obj K ◁ τ' ≫ (r' (U.obj K)).hom) hp.symm

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

/-- The section projection identity with an explicitly identified coefficient unit. -/
theorem section_projection_unit_iso
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {R : D ⥤ C} {G : D ⥤ C} {S : C ⥤ D}
    (adj : F ⊣ R) (adj' : G ⊣ S)
    (dF : (Functor.postcompose₂.obj F).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj (curriedTensor D))
    (dG : (Functor.postcompose₂.obj G).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj G).obj G).obj (curriedTensor C))
    (l : F ⋙ G ≅ 𝟭 C) (M U : C) (e : U ≅ 𝟙_ C)
    (hl : G.map ((dF.app M).app U) ≫
      (dG.app (F.obj M)).app (F.obj U) ≫
        (l.hom.app M ⊗ₘ l.hom.app U) = l.hom.app (M ⊗ U)) :
    let t := conjugateIsoEquiv (adj.comp adj') Adjunction.id l.symm
    let pF := adj.rightAdjointProjectionMap
      (T_C := (curriedTensor D).flip) (T_D := (curriedTensor C).flip)
      ((flipFunctor _ _ _).map dF)
    let pG := adj'.rightAdjointProjectionMap
      (T_C := (curriedTensor C).flip) (T_D := (curriedTensor D).flip)
      ((flipFunctor _ _ _).map dG)
    (ρ_ M).inv ≫ M ◁ e.inv ≫ M ◁ t.inv.app U ≫ (pF.app (S.obj U)).app M ≫
      R.map ((pG.app U).app (F.obj M) ≫
        S.map (l.hom.app M ▷ U ≫ M ◁ e.hom ≫ (ρ_ M).hom)) ≫
      t.hom.app M = 𝟙 M := by
  have hc := section_projection_composite adj adj' dF dG l M U hl
  let t := conjugateIsoEquiv (adj.comp adj') Adjunction.id l.symm
  have hn := t.hom.naturality (l.hom.app M ▷ U ≫ M ◁ e.hom ≫ (ρ_ M).hom)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.id_obj] at hn
  dsimp only
  rw [R.map_comp]
  simp only [Category.assoc]
  rw [hn]
  have hc' := congrArg
    (fun f ↦ (ρ_ M).inv ≫ M ◁ e.inv ≫ f ≫ M ◁ e.hom ≫ (ρ_ M).hom) hc
  simpa only [Category.assoc, Category.id_comp, Iso.inv_hom_id,
    ← whiskerLeft_comp_assoc, Iso.inv_hom_id_assoc, whiskerLeft_id,
    Category.comp_id, t, Functor.comp_obj] using hc'

/-- Inverse section projection with a chosen presentation of the coefficient unit. -/
theorem section_projection_inverse_iso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    {S : C ⥤ D} (R : D ⥤ C) (t : S ⋙ R ≅ 𝟭 C) (M U : C)
    (e : U ≅ 𝟙_ C) (V : D)
    (p : M ⊗ R.obj (S.obj U) ⟶ R.obj V) (q : V ⟶ S.obj M)
    [IsIso p] [IsIso q]
    (h : (ρ_ M).inv ≫ M ◁ e.inv ≫ M ◁ t.inv.app U ≫ p ≫ R.map q ≫
      t.hom.app M = 𝟙 M) :
    t.inv.app M ≫ R.map (inv q) ≫ inv p ≫
      M ◁ t.hom.app U ≫ M ◁ e.hom ≫ (ρ_ M).hom = 𝟙 M := by
  have he : asIso ((ρ_ M).inv ≫ M ◁ e.inv ≫ M ◁ t.inv.app U ≫ p ≫ R.map q ≫
      t.hom.app M) = Iso.refl M := Iso.ext h
  have hc := congrArg Iso.inv he
  simpa only [asIso_inv, Iso.refl_inv, IsIso.inv_comp, IsIso.Iso.inv_hom,
    IsIso.inv_id, IsIso.Iso.inv_inv, NatIso.inv_hom_app, NatIso.inv_inv_app,
    ← Functor.map_inv, inv_whiskerLeft, Category.assoc] using hc

/-- The supported scalar integral gives a contraction with the constant unit explicit. -/
theorem section_integral_tensor_iso
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] {F : C ⥤ D} {R : D ⥤ C} {S : C ⥤ D}
    (t : S ⋙ R ≅ 𝟭 C) (M U : C) (e : U ≅ 𝟙_ C) (V : D)
    (p : M ⊗ R.obj (S.obj U) ⟶ R.obj (F.obj M ⊗ S.obj U))
    (pV : M ⊗ R.obj V ⟶ R.obj (F.obj M ⊗ V))
    (q : F.obj M ⊗ S.obj U ⟶ S.obj M)
    [IsIso p] [IsIso pV] [IsIso q]
    (δ : S.obj U ⟶ V) (τ : R.obj V ⟶ U)
    (hp : p ≫ R.map (F.obj M ◁ δ) = (M ◁ R.map δ) ≫ pV)
    (hδ : t.inv.app U ≫ R.map δ ≫ τ = 𝟙 U)
    (h : t.inv.app M ≫ R.map (inv q) ≫ inv p ≫
      M ◁ t.hom.app U ≫ M ◁ e.hom ≫ (ρ_ M).hom = 𝟙 M) :
    t.inv.app M ≫ R.map (inv q) ≫ R.map (F.obj M ◁ δ) ≫
      inv pV ≫ M ◁ τ ≫ M ◁ e.hom ≫ (ρ_ M).hom = 𝟙 M := by
  have hn : R.map (F.obj M ◁ δ) ≫ inv pV = inv p ≫ M ◁ R.map δ := by
    apply (cancel_epi p).mp
    rw [← Category.assoc, hp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    simp only [IsIso.hom_inv_id_assoc]
  have hτ : R.map δ ≫ τ = t.hom.app U := by
    apply (cancel_epi (t.inv.app U)).mp
    rw [hδ, Iso.inv_hom_id_app]
    rfl
  rw [reassoc_of% hn, ← whiskerLeft_comp_assoc, hτ]
  exact h

/-- Pasting two constant-object units along a section gives its conjugate comparison. -/
theorem pasted_units_section
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {R : D ⥤ C} {G : D ⥤ C} {S : C ⥤ D}
    (a : F ⊣ R) (b : G ⊣ S) (l : F ⋙ G ≅ 𝟭 C)
    {U : C} {V : D} (c : F.obj U ⟶ V) (c' : G.obj V ⟶ U)
    (hc : G.map c ≫ c' = l.hom.app U) :
    (a.unit.app U ≫ R.map c) ≫ R.map (b.unit.app V ≫ S.map c') =
      (conjugateIsoEquiv Adjunction.id (a.comp b) l).hom.app U := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← R.map_comp_assoc, ← b.unit_naturality, R.map_comp]
  simp only [Category.assoc]
  rw [← R.map_comp, ← S.map_comp, hc]
  simp [conjugateEquiv_apply_app, Adjunction.comp_unit_app, Category.assoc]

/-- Transport a section unit across a natural direct-image comparison. -/
theorem section_comparison_naturality
    {C E D : Type*} [Category C] [Category E] [Category D]
    (S : C ⥤ E) (P Q : E ⥤ C) (R : C ⥤ D)
    (a : 𝟭 C ⟶ S ⋙ P) (a' : 𝟭 C ⟶ S ⋙ Q) (c : P ⋙ R ⟶ Q ⋙ R)
    (hc : ∀ M, R.map (a.app M) ≫ c.app (S.obj M) = R.map (a'.app M))
    (M : C) {V : E} (d : S.obj M ⟶ V) :
    R.map (a.app M ≫ P.map d) ≫ c.app V =
      R.map (a'.app M ≫ Q.map d) := by
  have hn := c.naturality d
  dsimp only [Functor.comp_map] at hn
  rw [R.map_comp, Category.assoc, hn, ← Category.assoc, hc, R.map_comp]

/-- Inserting an adjunction unit is the mate of its left-adjoint compositor. -/
theorem mate_composite_unit
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {R : D ⥤ C} {G : D ⥤ E} {S : E ⥤ D}
    {H : C ⥤ E} {T : E ⥤ C}
    (a : F ⊣ R) (b : G ⊣ S) (q : H ⊣ T) (l : H ⟶ F ⋙ G) (L : D) :
    R.map (b.unit.app L) ≫ (conjugateEquiv (a.comp b) q l).app (G.obj L) =
      (mateEquiv a q (TwoSquare.mk (𝟭 C) F H G l)).app L := by
  apply (q.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, H.map_comp, Category.assoc]
  rw [conjugateEquiv_counit, mateEquiv_counit]
  change H.map (R.map (b.unit.app L)) ≫ l.app (R.obj (S.obj (G.obj L))) ≫
      (a.comp b).counit.app (G.obj L) = l.app (R.obj L) ≫ G.map (a.counit.app L)
  have hn := l.naturality (R.map (b.unit.app L))
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  simp only [Adjunction.comp_counit_app]
  rw [← G.map_comp_assoc, a.counit_naturality]
  simp only [G.map_comp, Category.assoc]
  rw [b.left_triangle_components, Category.comp_id]

/-- Naturality of mates under a transformation of the bottom functor. -/
theorem mate_bottom_naturality
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {Q : C ⥤ D} {R : D ⥤ C} {H : E ⥤ F} {T : F ⥤ E}
    (a : Q ⊣ R) (b : H ⊣ T) {U : C ⥤ E} {V V' : D ⥤ F}
    (c : U ⋙ H ⟶ Q ⋙ V) (d : V ⟶ V') (M : D) :
    (mateEquiv a b (TwoSquare.mk U Q H V c)).app M ≫ T.map (d.app M) =
      (mateEquiv a b
        (TwoSquare.mk U Q H V' (c ≫ Functor.whiskerLeft Q d))).app M := by
  apply (b.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, H.map_comp, Category.assoc]
  rw [b.counit_naturality, ← Category.assoc, mateEquiv_counit, mateEquiv_counit]
  change (c.app (R.obj M) ≫ V.map (a.counit.app M)) ≫ d.app M =
    (c.app (R.obj M) ≫ d.app (Q.obj (R.obj M))) ≫ V'.map (a.counit.app M)
  simpa only [Category.assoc, Functor.comp_obj, Functor.id_obj] using
    congrArg (fun z ↦ c.app (R.obj M) ≫ z) (d.naturality (a.counit.app M))

/-- Pasting a square with a composite comparison inserts the corresponding unit. -/
theorem mate_chart_pasting
    {C D E F G : Type*} [Category C] [Category D] [Category E] [Category F] [Category G]
    {Q : C ⥤ D} {R : D ⥤ C} {P : E ⥤ F} {S : F ⥤ E}
    {J : F ⥤ G} {K : G ⥤ F} {H : E ⥤ G} {T : G ⥤ E}
    (a : Q ⊣ R) (b : P ⊣ S) (e : J ⊣ K) (h : H ⊣ T)
    {U : C ⥤ E} {V : D ⥤ F}
    (c : U ⋙ P ⟶ Q ⋙ V) (l : H ⟶ P ⋙ J) (M : D) :
    (mateEquiv a b (TwoSquare.mk U Q P V c)).app M ≫
        S.map (e.unit.app (V.obj M)) ≫
        (conjugateEquiv (b.comp e) h l).app (J.obj (V.obj M)) =
      (mateEquiv a h (TwoSquare.mk U Q H (V ⋙ J)
        (Functor.whiskerLeft U l ≫ Functor.whiskerRight c J))).app M := by
  rw [mate_composite_unit b e h l]
  apply (h.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, H.map_comp, Category.assoc]
  rw [mateEquiv_counit]
  dsimp only [TwoSquare.mk]
  have hn := l.naturality
    ((mateEquiv a b (TwoSquare.mk U Q P V c)).app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [reassoc_of% hn]
  simp only [← J.map_comp]
  have hr := mateEquiv_counit a h
    (TwoSquare.mk U Q H (V ⋙ J)
      (Functor.whiskerLeft U l ≫ Functor.whiskerRight c J)) M
  dsimp only [TwoSquare.mk, Functor.comp_obj] at hr
  rw [mateEquiv_counit, hr]
  simp only [TwoSquare.mk, J.map_comp, Functor.comp_map, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj,
    Functor.id_obj, Category.assoc]

end CategoryTheory.Adjunction
