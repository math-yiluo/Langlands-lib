/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap

/-!
# Compatibilities of projection maps

Let `adj : F ⊣ G` be an adjunction with `F : D ⥤ C`, let `T_C`, `T_D` be bifunctors (tensor
products, written `⊗`) and `φ : F (a ⊗ b) ⟶ F a ⊗ F b` a comparison. The right adjoint
projection map `π : G M ⊗ L ⟶ G (M ⊗ F L)`
(`CategoryTheory.Adjunction.rightAdjointProjectionMap`) satisfies the following
compatibilities.

* `CategoryTheory.Adjunction.unit_app_comp_map_rightAdjointProjectionMap`: the unit
  `η : N ⟶ G F N` is compatible with `π` and `φ`.
* `CategoryTheory.Adjunction.rightAdjointProjectionMap_mate`: `π` is compatible with the mate
  `G₁ ⋙ U ⟶ V ⋙ G₂` of a natural transformation `σ : U ⋙ F₂ ⟶ F₁ ⋙ V` compatible with the
  comparisons. This is the compatibility of the projection map with base change.
* `CategoryTheory.Adjunction.rightAdjointProjectionMap_comp`: the projection map of a
  composite of adjunctions is the composite of the projection maps.

Dually, for the projection map `F (K ⊗ G' M) ⟶ F K ⊗ M` of a left adjoint
(`CategoryTheory.Adjunction.projectionMap`):

* `CategoryTheory.Adjunction.projectionMap_mate`: it is compatible with the mate
  `U ⋙ F₂ ⟶ F₁ ⋙ V` of an isomorphism `G₁ ⋙ U ≅ V ⋙ G₂` compatible with the comparisons.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open _root_.CategoryTheory.Functor

section RightAdjoint

variable {C D : Type*} [Category* C] [Category* D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
  {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D}
  (φ : (postcompose₂.obj F).obj T_D ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj T_C)

/-- The unit `η : N ⟶ G F N` and the right adjoint projection map: the composite
`N ⊗ L ⟶ G F (N ⊗ L) ⟶ G (F N ⊗ F L)` of `η` and `G φ` is `η ⊗ 1` followed by the projection
map `G F N ⊗ L ⟶ G (F N ⊗ F L)`. -/
@[reassoc]
lemma unit_app_comp_map_rightAdjointProjectionMap (N L : D) :
    adj.unit.app ((T_D.obj N).obj L) ≫ G.map ((φ.app N).app L) =
      (T_D.map (adj.unit.app N)).app L ≫
        ((adj.rightAdjointProjectionMap φ).app (F.obj N)).app L := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, Category.assoc, adj.counit_naturality]
  erw [map_rightAdjointProjectionMap_app_app_comp_counit]
  have h₂ := NatTrans.congr_app (φ.naturality (adj.unit.app N)) L
  dsimp at h₂ ⊢
  rw [left_triangle_components_assoc, reassoc_of% h₂, ← NatTrans.comp_app, ← T_C.map_comp,
    adj.left_triangle_components, T_C.map_id, NatTrans.id_app, Category.comp_id]

/-- **The right adjoint projection map is compatible with conjugates.** Let `adj' : F' ⊣ G'` be
a second adjunction with a comparison `φ'`, and `α : F' ⟶ F` compatible with the comparisons.
Then the conjugate `β : G ⟶ G'` of `α` intertwines the projection maps:
`(β ⊗ 1) ≫ π' ≫ G'(1 ⊗ α) = π ≫ β`. -/
@[reassoc]
lemma rightAdjointProjectionMap_conjugate {F' : D ⥤ C} {G' : C ⥤ D} (adj' : F' ⊣ G')
    (φ' : (postcompose₂.obj F').obj T_D ⟶ (((whiskeringLeft₂ C).obj F').obj F').obj T_C)
    (α : F' ⟶ F)
    (hα : ∀ a b, α.app ((T_D.obj a).obj b) ≫ (φ.app a).app b =
      (φ'.app a).app b ≫ (T_C.map (α.app a)).app (F'.obj b) ≫
        (T_C.obj (F.obj a)).map (α.app b))
    (M : C) (L : D) :
    (T_D.map ((conjugateEquiv adj adj' α).app M)).app L ≫
        ((adj'.rightAdjointProjectionMap φ').app M).app L ≫
        G'.map ((T_C.obj M).map (α.app L)) =
      ((adj.rightAdjointProjectionMap φ).app M).app L ≫
        (conjugateEquiv adj adj' α).app ((T_C.obj M).obj (F.obj L)) := by
  apply (adj'.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, Category.assoc, adj'.counit_naturality,
    conjugateEquiv_counit]
  erw [map_rightAdjointProjectionMap_app_app_comp_counit_assoc]
  erw [α.naturality_assoc]
  erw [adj.map_rightAdjointProjectionMap_app_app_comp_counit φ M L]
  have h₁ := NatTrans.congr_app (φ'.naturality ((conjugateEquiv adj adj' α).app M)) L
  dsimp at h₁ ⊢
  rw [reassoc_of% h₁, ← NatTrans.comp_app_assoc, ← T_C.map_comp, conjugateEquiv_counit,
    reassoc_of% (hα (G.obj M) L), T_C.map_comp, NatTrans.comp_app]
  erw [(T_C.map (adj.counit.app M)).naturality (α.app L)]
  simp only [Category.assoc]
  rfl

variable {C₁ D₁ C₂ D₂ : Type*} [Category* C₁] [Category* D₁] [Category* C₂] [Category* D₂]
  {F₁ : D₁ ⥤ C₁} {G₁ : C₁ ⥤ D₁} (adj₁ : F₁ ⊣ G₁) {F₂ : D₂ ⥤ C₂} {G₂ : C₂ ⥤ D₂} (adj₂ : F₂ ⊣ G₂)
  {T₁ : C₁ ⥤ C₁ ⥤ C₁} {S₁ : D₁ ⥤ D₁ ⥤ D₁} {T₂ : C₂ ⥤ C₂ ⥤ C₂} {S₂ : D₂ ⥤ D₂ ⥤ D₂}
  (φ₁ : (postcompose₂.obj F₁).obj S₁ ⟶ (((whiskeringLeft₂ C₁).obj F₁).obj F₁).obj T₁)
  (φ₂ : (postcompose₂.obj F₂).obj S₂ ⟶ (((whiskeringLeft₂ C₂).obj F₂).obj F₂).obj T₂)
  {U : D₁ ⥤ D₂} {V : C₁ ⥤ C₂}
  (ψU : (postcompose₂.obj U).obj S₁ ⟶ (((whiskeringLeft₂ D₂).obj U).obj U).obj S₂)
  (ψV : (postcompose₂.obj V).obj T₁ ⟶ (((whiskeringLeft₂ C₂).obj V).obj V).obj T₂)
  (σ : U ⋙ F₂ ⟶ F₁ ⋙ V) (ex : G₁ ⋙ U ⟶ V ⋙ G₂)

/-- **The right adjoint projection map is compatible with mates.** Let `σ : U F₂ ⟶ F₁ V` be
compatible with the comparisons `φ₁`, `φ₂`, `ψ_U`, `ψ_V` (hypothesis `hσ`), and let
`ex : G₁ ⋙ U ⟶ V ⋙ G₂` be its mate (hypothesis `hex`, the transpose of `ex` along `adj₂`).
Then the square
```
U (G₁ M ⊗ L) --U π₁--> U G₁ (M ⊗ F₁ L) --ex--> G₂ V (M ⊗ F₁ L) --G₂ ψ_V--> G₂ (V M ⊗ V F₁ L)
     |                                                                         ‖
   ψ_U                                                                         ‖
     v                                                                         ‖
U G₁ M ⊗ U L --ex ⊗ 1--> G₂ V M ⊗ U L --π₂--> G₂ (V M ⊗ F₂ U L) --G₂(1 ⊗ σ)--> G₂ (V M ⊗ V F₁ L)
```
commutes. For derived pullbacks and pushforwards this is the compatibility of the projection
map with the base change map `Ex_*`. -/
lemma rightAdjointProjectionMap_mate
    (hσ : ∀ a b, F₂.map ((ψU.app a).app b) ≫ (φ₂.app (U.obj a)).app (U.obj b) ≫
      (T₂.map (σ.app a)).app _ ≫ (T₂.obj _).map (σ.app b) =
        σ.app ((S₁.obj a).obj b) ≫ V.map ((φ₁.app a).app b) ≫ (ψV.app _).app _)
    (hex : ∀ M, F₂.map (ex.app M) ≫ adj₂.counit.app (V.obj M) =
      σ.app (G₁.obj M) ≫ V.map (adj₁.counit.app M))
    (M : C₁) (L : D₁) :
    U.map (((adj₁.rightAdjointProjectionMap φ₁).app M).app L) ≫
        ex.app ((T₁.obj M).obj (F₁.obj L)) ≫ G₂.map ((ψV.app M).app (F₁.obj L)) =
      (ψU.app (G₁.obj M)).app L ≫ (S₂.map (ex.app M)).app (U.obj L) ≫
        ((adj₂.rightAdjointProjectionMap φ₂).app (V.obj M)).app (U.obj L) ≫
        G₂.map ((T₂.obj (V.obj M)).map (σ.app L)) := by
  apply (adj₂.homEquiv _ _).symm.injective
  simp only [homEquiv_counit, Functor.map_comp, Category.assoc]
  dsimp
  -- the right hand side
  erw [adj₂.counit_naturality ((T₂.obj (V.obj M)).map (σ.app L))]
  erw [map_rightAdjointProjectionMap_app_app_comp_counit_assoc]
  have h₁ := NatTrans.congr_app (φ₂.naturality (ex.app M)) (U.obj L)
  dsimp at h₁
  rw [reassoc_of% h₁, ← NatTrans.comp_app_assoc, ← T₂.map_comp, hex]
  -- the left hand side
  rw [adj₂.counit_naturality]
  have h₂ := hex ((T₁.obj M).obj (F₁.obj L))
  dsimp at h₂
  rw [reassoc_of% h₂]
  have h₃ := σ.naturality (((adj₁.rightAdjointProjectionMap φ₁).app M).app L)
  dsimp at h₃
  rw [reassoc_of% h₃, ← V.map_comp_assoc]
  erw [map_rightAdjointProjectionMap_app_app_comp_counit]
  have h₄ := NatTrans.congr_app (ψV.naturality (adj₁.counit.app M)) (F₁.obj L)
  dsimp at h₄
  rw [V.map_comp_assoc, h₄]
  have h₅ := hσ (G₁.obj M) L
  simp only [← Category.assoc] at h₅ ⊢
  rw [← h₅]
  simp only [Category.assoc]
  congr 2
  rw [T₂.map_comp, NatTrans.comp_app_assoc]
  congr 1
  exact ((T₂.map (V.map (adj₁.counit.app M))).naturality (σ.app L))

section Comp

variable {B : Type*} [Category* B] {F₁ : D₁ ⥤ C₁} {G₁ : C₁ ⥤ D₁} (adj₁ : F₁ ⊣ G₁) {F₂ : C₁ ⥤ B}
  {G₂ : B ⥤ C₁} (adj₂ : F₂ ⊣ G₂) {T_B : B ⥤ B ⥤ B}
  (φ₁ : (postcompose₂.obj F₁).obj S₁ ⟶ (((whiskeringLeft₂ C₁).obj F₁).obj F₁).obj T₁)
  (φ₂ : (postcompose₂.obj F₂).obj T₁ ⟶ (((whiskeringLeft₂ B).obj F₂).obj F₂).obj T_B)
  (φ₁₂ : (postcompose₂.obj (F₁ ⋙ F₂)).obj S₁ ⟶
    (((whiskeringLeft₂ B).obj (F₁ ⋙ F₂)).obj (F₁ ⋙ F₂)).obj T_B)

/-- **The projection map of a composite of adjunctions** is the composite of the projection
maps, for the composite comparison `F₂ (F₁ (a ⊗ b)) ⟶ F₂ (F₁ a ⊗ F₁ b) ⟶ F₂ F₁ a ⊗ F₂ F₁ b`. -/
lemma rightAdjointProjectionMap_comp
    (hφ : ∀ a b, (φ₁₂.app a).app b =
      F₂.map ((φ₁.app a).app b) ≫ (φ₂.app (F₁.obj a)).app (F₁.obj b))
    (M : B) (L : D₁) :
    (((adj₁.comp adj₂).rightAdjointProjectionMap φ₁₂).app M).app L =
      ((adj₁.rightAdjointProjectionMap φ₁).app (G₂.obj M)).app L ≫
        G₁.map (((adj₂.rightAdjointProjectionMap φ₂).app M).app (F₁.obj L)) := by
  apply ((adj₁.comp adj₂).homEquiv _ _).symm.injective
  rw [homEquiv_symm_rightAdjointProjectionMap_app_app, comp_homEquiv]
  dsimp only [Equiv.symm_trans_apply]
  erw [homEquiv_naturality_right_symm, homEquiv_symm_rightAdjointProjectionMap_app_app,
    homEquiv_naturality_left_symm, homEquiv_symm_rightAdjointProjectionMap_app_app]
  rw [hφ]
  have h₁ := NatTrans.congr_app (φ₂.naturality (adj₁.counit.app (G₂.obj M))) (F₁.obj L)
  dsimp at h₁ ⊢
  rw [Functor.map_comp_assoc, reassoc_of% h₁, comp_counit_app, T_B.map_comp,
    NatTrans.comp_app]
  simp only [Category.assoc]

end Comp

end RightAdjoint

section LeftAdjoint

variable {C₁ D₁ C₂ D₂ : Type*} [Category* C₁] [Category* D₁] [Category* C₂] [Category* D₂]
  {F₁ : C₁ ⥤ D₁} {G₁ : D₁ ⥤ C₁} (adj₁ : F₁ ⊣ G₁) {F₂ : C₂ ⥤ D₂} {G₂ : D₂ ⥤ C₂} (adj₂ : F₂ ⊣ G₂)
  (G'₁ : D₁ ⥤ C₁) (G'₂ : D₂ ⥤ C₂)
  {T₁ : C₁ ⥤ C₁ ⥤ C₁} {T'₁ : D₁ ⥤ D₁ ⥤ D₁} {T₂ : C₂ ⥤ C₂ ⥤ C₂} {T'₂ : D₂ ⥤ D₂ ⥤ D₂}
  (δ₁ : (((whiskeringLeft₂ C₁).obj G₁).obj G'₁).obj T₁ ⟶ (postcompose₂.obj G₁).obj T'₁)
  (δ₂ : (((whiskeringLeft₂ C₂).obj G₂).obj G'₂).obj T₂ ⟶ (postcompose₂.obj G₂).obj T'₂)
  {U : C₁ ⥤ C₂} {V : D₁ ⥤ D₂}
  (ψU : (postcompose₂.obj U).obj T₁ ⟶ (((whiskeringLeft₂ C₂).obj U).obj U).obj T₂)
  (ψV : (postcompose₂.obj V).obj T'₁ ⟶ (((whiskeringLeft₂ D₂).obj V).obj V).obj T'₂)
  (τ : G₁ ⋙ U ⟶ V ⋙ G₂) (τ' : G'₁ ⋙ U ⟶ V ⋙ G'₂) (β : U ⋙ F₂ ⟶ F₁ ⋙ V)

lemma projectionMapTranspose_app_app (K : C₁) (M : D₁) :
    ((adj₁.projectionMapTranspose G'₁ T₁ T'₁ δ₁).app K).app M =
      (T₁.map (adj₁.unit.app K)).app (G'₁.obj M) ≫ (δ₁.app (F₁.obj K)).app M :=
  rfl

/-- **The projection map of a left adjoint is compatible with mates.** Let `β : U F₂ ⟶ F₁ V` be
the mate of `τ : G₁ ⋙ U ⟶ V ⋙ G₂` (hypothesis `hβ`), and let `τ`, `τ'` be compatible with the
comparisons `δ₁`, `δ₂`, `ψ_U`, `ψ_V` (hypothesis `hδ`). Then the square
```
F₂ U (K ⊗ G'₁ M) --β--> V F₁ (K ⊗ G'₁ M) --V π₁--> V (F₁ K ⊗ M) --ψ_V--> V F₁ K ⊗ V M
       |                                                                  ‖
 F₂ ψ_U ≫ F₂(1 ⊗ τ')                                                       ‖
       v                                                                  ‖
F₂ (U K ⊗ G'₂ V M) ------------π₂------------> F₂ U K ⊗ V M ---β ⊗ 1---> V F₁ K ⊗ V M
```
commutes. For the extension by zero along an open immersion this is the compatibility of the
projection formula with base change. -/
lemma projectionMap_mate
    (hβ : ∀ K, adj₂.unit.app (U.obj K) ≫ G₂.map (β.app K) =
      U.map (adj₁.unit.app K) ≫ τ.app (F₁.obj K))
    (hδ : ∀ X Y, U.map ((δ₁.app X).app Y) ≫ τ.app ((T'₁.obj X).obj Y) ≫
        G₂.map ((ψV.app X).app Y) =
      (ψU.app (G₁.obj X)).app (G'₁.obj Y) ≫ (T₂.map (τ.app X)).app _ ≫
        (T₂.obj _).map (τ'.app Y) ≫ (δ₂.app (V.obj X)).app (V.obj Y))
    (K : C₁) (M : D₁) :
    β.app ((T₁.obj K).obj (G'₁.obj M)) ≫
        V.map (((adj₁.projectionMap G'₁ T₁ T'₁ δ₁).app K).app M) ≫
        (ψV.app (F₁.obj K)).app M =
      F₂.map ((ψU.app K).app (G'₁.obj M)) ≫ F₂.map ((T₂.obj (U.obj K)).map (τ'.app M)) ≫
        ((adj₂.projectionMap G'₂ T₂ T'₂ δ₂).app (U.obj K)).app (V.obj M) ≫
        (T'₂.map (β.app K)).app (V.obj M) := by
  apply (adj₂.homEquiv _ _).injective
  simp only [homEquiv_unit, Functor.map_comp]
  dsimp
  -- the left hand side
  rw [reassoc_of% (hβ _)]
  have h₁ := τ.naturality (((adj₁.projectionMap G'₁ T₁ T'₁ δ₁).app K).app M)
  dsimp at h₁
  rw [← reassoc_of% h₁, ← U.map_comp_assoc]
  erw [unit_app_comp_map_projectionMap_app_app]
  rw [projectionMapTranspose_app_app, U.map_comp_assoc, hδ]
  -- the right hand side
  rw [adj₂.unit_naturality_assoc, adj₂.unit_naturality_assoc]
  erw [unit_app_comp_map_projectionMap_app_app_assoc]
  rw [projectionMapTranspose_app_app]
  have h₂ := NatTrans.congr_app (δ₂.naturality (β.app K)) (V.obj M)
  dsimp at h₂
  rw [Category.assoc, ← h₂, ← NatTrans.comp_app_assoc, ← T₂.map_comp, hβ]
  have h₃ := NatTrans.congr_app (ψU.naturality (adj₁.unit.app K)) (G'₁.obj M)
  dsimp at h₃
  rw [reassoc_of% h₃, T₂.map_comp, NatTrans.comp_app_assoc]
  congr 1
  conv_lhs => rw [← NatTrans.comp_app_assoc, ← T₂.map_comp]
  conv_rhs => rw [← NatTrans.comp_app_assoc, ← T₂.map_comp]
  exact ((T₂.map (U.map (adj₁.unit.app K) ≫ τ.app (F₁.obj K))).naturality_assoc (τ'.app M) _).symm

end LeftAdjoint

end CategoryTheory.Adjunction
