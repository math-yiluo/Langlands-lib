/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Transport of mates along comparison functors

Given two squares of adjunctions and comparison functors between them, compatible with the
left adjoints, a natural transformation compatible with the comparisons has a mate that is
compatible with the comparisons, the right adjoints being compared by the mates of the
left-adjoint comparisons.

Source: Weil conjectures blueprint, node proposition-composition-base-change-rf-shriek--4, proof
step 8 (blueprint: proposition-composition-base-change-rf-shriek--4).
-/

@[expose] public section

open CategoryTheory Functor

namespace CategoryTheory

variable {S V T W S' V' T' W' : Type*} [Category S] [Category V] [Category T] [Category W]
  [Category S'] [Category V'] [Category T'] [Category W']
  {L₁ : S ⥤ V} {R₁ : V ⥤ S} (adj₁ : L₁ ⊣ R₁) {L₂ : T ⥤ W} {R₂ : W ⥤ T} (adj₂ : L₂ ⊣ R₂)
  {L₁' : S' ⥤ V'} {R₁' : V' ⥤ S'} (adj₁' : L₁' ⊣ R₁')
  {L₂' : T' ⥤ W'} {R₂' : W' ⥤ T'} (adj₂' : L₂' ⊣ R₂')

/-- The unit of an adjunction, transported along a comparison of left adjoints. -/
theorem map_unit_comp_mateEquiv_app {ΦS : S ⥤ S'} {ΦV : V ⥤ V'}
    (φ : L₁ ⋙ ΦV ≅ ΦS ⋙ L₁') (x : S) :
    ΦS.map (adj₁.unit.app x) ≫ (mateEquiv adj₁ adj₁' φ.inv).app (L₁.obj x) =
      adj₁'.unit.app (ΦS.obj x) ≫ R₁'.map (φ.inv.app x) :=
  unit_mateEquiv adj₁ adj₁' φ.inv x

/-- The counit of an adjunction, transported along a comparison of left adjoints. -/
theorem map_mateEquiv_app_comp_counit {ΦS : S ⥤ S'} {ΦV : V ⥤ V'}
    (φ : L₁ ⋙ ΦV ≅ ΦS ⋙ L₁') (y : V) :
    L₁'.map ((mateEquiv adj₁ adj₁' φ.inv).app y) ≫ adj₁'.counit.app (ΦV.obj y) =
      φ.inv.app (R₁.obj y) ≫ ΦV.map (adj₁.counit.app y) :=
  mateEquiv_counit adj₁ adj₁' φ.inv y

/-- The components of a mate. -/
private theorem mateEquiv_app_eq {G : S ⥤ T} {H : V ⥤ W} (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (y : V) :
    (mateEquiv adj₁ adj₂ α).app y =
      adj₂.unit.app (G.obj (R₁.obj y)) ≫ R₂.map (α.app (R₁.obj y)) ≫
        R₂.map (H.map (adj₁.counit.app y)) := by
  simp [mateEquiv]

/-- Mates are transported along comparison functors compatible with the left adjoints.
If `α` corresponds to `α'` under the comparisons, then the mate of `α` corresponds to the
mate of `α'`, the right adjoints being compared by the mates of the left comparisons. -/
theorem mateEquiv_app_transport {G : S ⥤ T} {H : V ⥤ W} {G' : S' ⥤ T'} {H' : V' ⥤ W'}
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (α' : G' ⋙ L₂' ⟶ L₁' ⋙ H')
    {ΦS : S ⥤ S'} {ΦV : V ⥤ V'} {ΦT : T ⥤ T'} {ΦW : W ⥤ W'}
    (φ₁ : L₁ ⋙ ΦV ≅ ΦS ⋙ L₁') (φ₂ : L₂ ⋙ ΦW ≅ ΦT ⋙ L₂')
    (θG : G ⋙ ΦT ≅ ΦS ⋙ G') (θH : H ⋙ ΦW ≅ ΦV ⋙ H')
    (hα : ∀ x : S, ΦW.map (α.app x) =
      φ₂.hom.app (G.obj x) ≫ L₂'.map (θG.hom.app x) ≫ α'.app (ΦS.obj x) ≫
        H'.map (φ₁.inv.app x) ≫ θH.inv.app (L₁.obj x)) (y : V) :
    ΦT.map ((mateEquiv adj₁ adj₂ α).app y) ≫
        (mateEquiv adj₂ adj₂' φ₂.inv).app (H.obj y) =
      θG.hom.app (R₁.obj y) ≫ G'.map ((mateEquiv adj₁ adj₁' φ₁.inv).app y) ≫
        (mateEquiv adj₁' adj₂' α').app (ΦV.obj y) ≫ R₂'.map (θH.inv.app y) := by
  have e₁ := mateEquiv_app_eq adj₁ adj₂ α y
  have e₂ := mateEquiv_app_eq adj₁' adj₂' α' (ΦV.obj y)
  have n₂ : ∀ {a b : W} (f : a ⟶ b), ΦT.map (R₂.map f) ≫
      (mateEquiv adj₂ adj₂' φ₂.inv).app b =
      (mateEquiv adj₂ adj₂' φ₂.inv).app a ≫ R₂'.map (ΦW.map f) :=
    fun f ↦ (mateEquiv adj₂ adj₂' φ₂.inv).naturality f
  have u₂ := map_unit_comp_mateEquiv_app adj₂ adj₂' φ₂ (G.obj (R₁.obj y))
  have c₁ := map_mateEquiv_app_comp_counit adj₁ adj₁' φ₁ y
  have hθ := θH.inv.naturality (adj₁.counit.app y)
  have hθG := adj₂'.unit.naturality (θG.hom.app (R₁.obj y) ≫
    G'.map ((mateEquiv adj₁ adj₁' φ₁.inv).app y))
  have hα' := α'.naturality ((mateEquiv adj₁ adj₁' φ₁.inv).app y)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hθ hθG hα'
  rw [e₁, e₂]
  simp only [Functor.map_comp, Category.assoc]
  erw [n₂ (H.map (adj₁.counit.app y)), reassoc_of% (n₂ (α.app (R₁.obj y))), reassoc_of% u₂]
  rw [← R₂'.map_comp_assoc, hα]
  simp only [Iso.inv_hom_id_app_assoc, Functor.map_comp, Category.assoc]
  rw [← R₂'.map_comp, ← hθ]
  simp only [Functor.map_comp, Category.assoc] at hθG ⊢
  rw [reassoc_of% hθG]
  congr 2
  rw [← R₂'.map_comp_assoc (L₂'.map (G'.map _)), hα']
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  rw [← R₂'.map_comp_assoc, ← H'.map_comp, ← c₁, H'.map_comp, R₂'.map_comp_assoc]

end CategoryTheory
