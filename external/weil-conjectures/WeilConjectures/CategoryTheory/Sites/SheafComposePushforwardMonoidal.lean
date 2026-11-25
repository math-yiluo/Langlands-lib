/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal

/-!
# Postcomposition and pushforward of sheaves commute monoidally

Let `G : A ⥤ B` be a lax monoidal functor preserving sheaves and `F : C ⥤ D` a continuous
functor of sites. The postcomposition `G_* = sheafCompose G` and the pushforward `F_*` commute
strictly: `F_* (G_* P)` and `G_* (F_* P)` are both the presheaf `F.op ⋙ P ⋙ G`. We show that
this identification is monoidal for the lax structures of `G_*` and `F_*`.

## Main results

- `CategoryTheory.μ_sheafToPresheaf_comp_map_μ_sheafCompose`: the tensor map of `G_*` read on
  underlying presheaves is the postcomposition with `G` of the tensor map of `sheafToPresheaf`,
  preceded by the tensor map of `G` (the analogue of
  `CategoryTheory.Functor.μ_sheafToPresheaf_comp_map_μ_sheafPushforwardContinuous`).
- `CategoryTheory.Functor.isMonoidal_sheafPushforwardContinuousCompSheafComposeIso_hom`: the
  identification `F_* ⋙ G_* ≅ G_* ⋙ F_*` is monoidal.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal

attribute [local instance] Sheaf.monoidalCategory

section

variable {C : Type*} [Category C] (J : GrothendieckTopology C)
  {A : Type*} [Category A] [MonoidalCategory A]
  {B : Type*} [Category B] [MonoidalCategory B]
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  [(J.W (A := B)).IsMonoidal] [HasWeakSheafify J B]
  (G : A ⥤ B) [J.HasSheafCompose G] [G.LaxMonoidal]

omit [MonoidalCategory A] [MonoidalCategory B]
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A] [(J.W (A := B)).IsMonoidal] [G.LaxMonoidal] in
lemma sheafToPresheafCompWhiskeringRightIsoSheafCompose_hom_app (P : Sheaf J A) :
    (sheafToPresheafCompWhiskeringRightIsoSheafCompose J G).hom.app P = 𝟙 _ := by
  have := (sheafificationAdjunction J B).right_triangle_components ((sheafCompose J G).obj P)
  simp only [sheafToPresheafCompWhiskeringRightIsoSheafCompose,
    sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso] at this ⊢
  simp
  rfl

/-- The tensor map `μ` of the lax monoidal postcomposition `G_*` of sheaves, read on underlying
presheaves after `μ` of the lax monoidal functor `sheafToPresheaf`, is the postcomposition with
`G` of `μ` of `sheafToPresheaf`, preceded by the tensor map of postcomposition with `G` on
presheaves. -/
lemma μ_sheafToPresheaf_comp_map_μ_sheafCompose (P Q : Sheaf J A) :
    μ (sheafToPresheaf J B) ((sheafCompose J G).obj P) ((sheafCompose J G).obj Q) ≫
      (sheafToPresheaf J B).map (μ (sheafCompose J G) P Q) =
    μ ((Functor.whiskeringRight _ _ _).obj G) P.obj Q.obj ≫
      ((Functor.whiskeringRight _ _ _).obj G).map (μ (sheafToPresheaf J A) P Q) := by
  have h := NatTrans.IsMonoidal.tensor
    (τ := (sheafToPresheafCompWhiskeringRightIsoSheafCompose J G).hom) P Q
  rw [sheafToPresheafCompWhiskeringRightIsoSheafCompose_hom_app,
    sheafToPresheafCompWhiskeringRightIsoSheafCompose_hom_app,
    sheafToPresheafCompWhiskeringRightIsoSheafCompose_hom_app, comp_μ, comp_μ] at h
  simpa using h.symm


/-- The unit `ε` of the lax monoidal postcomposition `G_*` of sheaves, read on underlying
presheaves after the unit of `sheafToPresheaf`, is the postcomposition with `G` of the unit of
`sheafToPresheaf`, preceded by the unit of postcomposition with `G` on presheaves. -/
lemma ε_sheafToPresheaf_comp_map_ε_sheafCompose :
    ε (sheafToPresheaf J B) ≫ (sheafToPresheaf J B).map (ε (sheafCompose J G)) =
      ε ((Functor.whiskeringRight _ _ _).obj G) ≫
        ((Functor.whiskeringRight _ _ _).obj G).map (ε (sheafToPresheaf J A)) := by
  have h := NatTrans.IsMonoidal.unit
    (τ := (sheafToPresheafCompWhiskeringRightIsoSheafCompose J G).hom)
  rw [sheafToPresheafCompWhiskeringRightIsoSheafCompose_hom_app, comp_ε, comp_ε] at h
  simpa using h.symm

end

namespace Functor

variable {C : Type*} [Category C] {D : Type*} [Category D] (F : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [F.IsContinuous J K]
  {A : Type*} [Category A] [MonoidalCategory A] [BraidedCategory A]
  {B : Type*} [Category B] [MonoidalCategory B] [BraidedCategory B]
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  [(J.W (A := B)).IsMonoidal] [HasWeakSheafify J B]
  [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]
  [(K.W (A := B)).IsMonoidal] [HasWeakSheafify K B]
  (G : A ⥤ B) [J.HasSheafCompose G] [K.HasSheafCompose G] [G.LaxMonoidal]

/-- The pushforward `F_*` commutes with the postcomposition `G_*`: both composites send a sheaf
`P` to the presheaf `F.op ⋙ P ⋙ G`. -/
abbrev sheafPushforwardContinuousCompSheafComposeIso :
    F.sheafPushforwardContinuous A J K ⋙ sheafCompose J G ≅
      sheafCompose K G ⋙ F.sheafPushforwardContinuous B J K :=
  Iso.refl _

/-- The identification `F_* ⋙ G_* ≅ G_* ⋙ F_*` is monoidal. -/
instance isMonoidal_sheafPushforwardContinuousCompSheafComposeIso_hom :
    NatTrans.IsMonoidal (sheafPushforwardContinuousCompSheafComposeIso F J K G).hom where
  unit := by
    apply Sheaf.hom_ext_of_ε_comp
    ext U
    have h₁ := congr_app (ε_sheafToPresheaf_comp_map_ε_sheafCompose J G (A := A)) U
    have h₂ := ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app F A J K U
    have h₃ := ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app F B J K U
    have h₄ := congr_app (ε_sheafToPresheaf_comp_map_ε_sheafCompose K G (A := A)) (F.op.obj U)
    simp only [NatTrans.comp_app] at h₁ h₄
    simp only [comp_ε, Iso.refl_hom, NatTrans.id_app, Category.comp_id, Functor.map_comp,
      NatTrans.comp_app]
    erw [← Category.assoc, h₁, ← Category.assoc, h₃, h₄]
    simp only [Category.assoc]
    congr 1
    erw [← Functor.map_comp, h₂]
    rfl
  tensor P Q := by
    apply Sheaf.hom_ext_of_μ_comp
    ext U
    have h₁ := congr_app (μ_sheafToPresheaf_comp_map_μ_sheafCompose J G
      ((F.sheafPushforwardContinuous A J K).obj P)
      ((F.sheafPushforwardContinuous A J K).obj Q)) U
    have h₂ := μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app F A J K P Q U
    have h₃ := μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app F B J K
      ((sheafCompose K G).obj P) ((sheafCompose K G).obj Q) U
    have h₄ := congr_app (μ_sheafToPresheaf_comp_map_μ_sheafCompose K G P Q) (F.op.obj U)
    simp only [NatTrans.comp_app] at h₁ h₄
    simp only [comp_μ, Iso.refl_hom, NatTrans.id_app, Category.comp_id, tensorHom_id,
      id_whiskerRight, Category.id_comp, Functor.map_comp, NatTrans.comp_app]
    erw [← Category.assoc, h₁, ← Category.assoc, h₃, h₄]
    simp only [Category.assoc]
    congr 1
    erw [← Functor.map_comp, h₂]
    rfl

end Functor

end CategoryTheory
