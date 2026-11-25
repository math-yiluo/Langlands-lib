/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Enriched.FunctorCategory

/-!
# Enriched homs and precomposition with an equivalence

If `G : K ⥤ J` is an equivalence, the morphism
`precompEnrichedHom V F₁ F₂ G : enrichedHom V F₁ F₂ ⟶ enrichedHom V (G ⋙ F₁) (G ⋙ F₂)` induced by
precomposition with `G` is an isomorphism
(`CategoryTheory.Enriched.FunctorCategory.isIso_precompEnrichedHom`): an end is invariant under
reindexing along an equivalence. The inverse is built from the projections at chosen preimages
`G.objPreimage j`.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.Enriched.FunctorCategory

open Category MonoidalCategory Limits

variable (V : Type u₁) [Category.{v₁} V] [MonoidalCategory V]
  {C : Type u₂} [Category.{v₂} C] {J : Type u₃} [Category.{v₃} J]
  {K : Type u₄} [Category.{v₄} K] [EnrichedOrdinaryCategory V C]
  (F₁ F₂ : J ⥤ C) (G : K ⥤ J) [G.IsEquivalence]
  [HasEnrichedHom V F₁ F₂] [HasEnrichedHom V (G ⋙ F₁) (G ⋙ F₂)]

/-- The inverse of `precompEnrichedHom` along an equivalence `G`: the projection to `F₁ j ⟶ F₂ j`
is the projection at `G.objPreimage j`, transported along `G.obj (G.objPreimage j) ≅ j`. -/
noncomputable def precompEnrichedHomInv :
    enrichedHom V (G ⋙ F₁) (G ⋙ F₂) ⟶ enrichedHom V F₁ F₂ :=
  end_.lift (fun j ↦ enrichedHomπ V (G ⋙ F₁) (G ⋙ F₂) (G.objPreimage j) ≫
      eHomWhiskerRight V (F₁.map (G.objObjPreimageIso j).inv) _ ≫
      eHomWhiskerLeft V _ (F₂.map (G.objObjPreimageIso j).hom)) (fun i j f ↦ by
    simp only [diagram_obj_map, diagram_map_app, Quiver.Hom.unop_op]
    let g := G.preimage ((G.objObjPreimageIso i).hom ≫ f ≫ (G.objObjPreimageIso j).inv)
    have hg : G.map g = (G.objObjPreimageIso i).hom ≫ f ≫ (G.objObjPreimageIso j).inv :=
      G.map_preimage _
    have h1 : (G.objObjPreimageIso i).hom ≫ f = G.map g ≫ (G.objObjPreimageIso j).hom := by
      simp [hg]
    have h2 : (G.objObjPreimageIso i).inv ≫ G.map g = f ≫ (G.objObjPreimageIso j).inv := by
      simp [hg]
    have hc := enrichedHom_condition V (G ⋙ F₁) (G ⋙ F₂) g
    simp only [Functor.comp_map, Functor.comp_obj] at hc
    simp only [assoc]
    rw [← eHomWhiskerLeft_comp, ← F₂.map_comp, h1, F₂.map_comp, eHomWhiskerLeft_comp,
      ← eHom_whisker_exchange_assoc, reassoc_of% hc, ← eHomWhiskerRight_comp_assoc,
      ← F₁.map_comp, h2, eHom_whisker_exchange, F₁.map_comp, eHomWhiskerRight_comp_assoc]
    rfl)

/-- The projections of `precompEnrichedHomInv`. -/
lemma precompEnrichedHomInv_π (j : J) :
    precompEnrichedHomInv V F₁ F₂ G ≫ enrichedHomπ V F₁ F₂ j =
      enrichedHomπ V (G ⋙ F₁) (G ⋙ F₂) (G.objPreimage j) ≫
        eHomWhiskerRight V (F₁.map (G.objObjPreimageIso j).inv) _ ≫
        eHomWhiskerLeft V _ (F₂.map (G.objObjPreimageIso j).hom) :=
  end_.lift_π _ _ _

omit [G.IsEquivalence] in
/-- The projections of `precompEnrichedHom`. -/
lemma precompEnrichedHom_π (k : K) :
    precompEnrichedHom V F₁ F₂ G ≫ enrichedHomπ V (G ⋙ F₁) (G ⋙ F₂) k =
      enrichedHomπ V F₁ F₂ (G.obj k) := by
  simp [precompEnrichedHom, precompEnrichedHom']

/-- Precomposition with an equivalence induces an isomorphism of enriched homs. -/
instance isIso_precompEnrichedHom : IsIso (precompEnrichedHom V F₁ F₂ G) := by
  refine ⟨precompEnrichedHomInv V F₁ F₂ G, ?_, ?_⟩
  · ext j
    rw [assoc, precompEnrichedHomInv_π, id_comp, reassoc_of% precompEnrichedHom_π,
      ← eHom_whisker_exchange,
      reassoc_of% enrichedHom_condition V F₁ F₂ (G.objObjPreimageIso j).hom,
      ← eHomWhiskerRight_comp, ← F₁.map_comp, Iso.inv_hom_id, F₁.map_id, eHomWhiskerRight_id,
      comp_id]
  · ext k
    have hc := enrichedHom_condition V (G ⋙ F₁) (G ⋙ F₂)
      (G.preimage (G.objObjPreimageIso (G.obj k)).hom)
    simp only [Functor.comp_map, Functor.comp_obj, Functor.map_preimage] at hc
    rw [assoc, precompEnrichedHom_π, precompEnrichedHomInv_π, id_comp, ← eHom_whisker_exchange,
      reassoc_of% hc, ← eHomWhiskerRight_comp, ← F₁.map_comp, Iso.inv_hom_id, F₁.map_id,
      eHomWhiskerRight_id, comp_id]

end CategoryTheory.Enriched.FunctorCategory
