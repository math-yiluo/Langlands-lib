/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering

/-!
# Curried forms of comparisons of bifunctors

A natural isomorphism `T ⋙ H ≅ H.prod H' ⋙ T'` between functors out of a product category
induces the corresponding natural isomorphism of curried bifunctors
`H (T a b) ≅ T' (H a) (H' b)`, in the form used by
`CategoryTheory.Adjunction.rightAdjointProjectionMap` and
`CategoryTheory.Adjunction.ComparisonCompatible`.
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

/-- The curried form `H (T a b) ≅ T' (H a) (H b)` of a natural isomorphism
`T ⋙ H ≅ H.prod H ⋙ T'`. -/
@[simps!]
def curryCompIsoOfIso {T : C × C ⥤ C} {H : C ⥤ D} {T' : D × D ⥤ D}
    (e : T ⋙ H ≅ H.prod H ⋙ T') :
    (postcompose₂.obj H).obj (curry.obj T) ≅
      (((whiskeringLeft₂ D).obj H).obj H).obj (curry.obj T') :=
  NatIso.ofComponents (fun a ↦ NatIso.ofComponents (fun b ↦ e.app (a, b)) (fun {b b'} f ↦ by
      have h := e.hom.naturality (Prod.mkHom (𝟙 a) f)
      dsimp at h ⊢
      rw [h, CategoryTheory.Functor.map_id]))
    (fun {a a'} f ↦ by
      ext b
      have h := e.hom.naturality (Prod.mkHom f (𝟙 b))
      dsimp at h ⊢
      rw [h, CategoryTheory.Functor.map_id])

/-- The curried form `H (T a b) ≅ T' (H a) (H b)` of a natural isomorphism
`T ⋙ H ≅ H.prod H ⋙ T'`, with `T'` already curried. -/
@[simps!]
def curryCompIsoOfIso' {T : C × C ⥤ C} {H : C ⥤ D} {T' : D ⥤ D ⥤ D}
    (e : T ⋙ H ≅ H.prod H ⋙ uncurry.obj T') :
    (postcompose₂.obj H).obj (curry.obj T) ≅
      (((whiskeringLeft₂ D).obj H).obj H).obj T' :=
  NatIso.ofComponents (fun a ↦ NatIso.ofComponents (fun b ↦ e.app (a, b)) (fun {b b'} f ↦ by
      have h := e.hom.naturality (Prod.mkHom (𝟙 a) f)
      dsimp at h ⊢
      simp [h]))
    (fun {a a'} f ↦ by
      ext b
      have h := e.hom.naturality (Prod.mkHom f (𝟙 b))
      dsimp at h ⊢
      simp [h])

/-- The naturality, in uncurried form, of a natural transformation
`G M ⊗ L ⟶ G (M ⊗ F L)` of bifunctors between curried tensor products, restricted along
functors `ιC` and `ιD`. -/
lemma naturality_curry_postcompose₂ {C' D' : Type*} [Category* C'] [Category* D']
    {F : D ⥤ C} {G : C ⥤ D} {T_C : C × C ⥤ C} {T_D : D × D ⥤ D}
    (α : G ⋙ curry.obj T_D ⟶
      (postcompose₂.obj G).obj ((((whiskeringLeft₂ C).obj (𝟭 C)).obj F).obj (curry.obj T_C)))
    (ιC : C' ⥤ C) (ιD : D' ⥤ D) {M M' : C'} {L L' : D'} (f₁ : M ⟶ M') (f₂ : L ⟶ L') :
    T_D.map (Prod.mkHom (G.map (ιC.map f₁)) (ιD.map f₂)) ≫
        (α.app (ιC.obj M')).app (ιD.obj L') =
      (α.app (ιC.obj M)).app (ιD.obj L) ≫
        G.map (T_C.map (Prod.mkHom (ιC.map f₁) (F.map (ιD.map f₂)))) := by
  have e₁ : Prod.mkHom (G.map (ιC.map f₁)) (ιD.map f₂) =
      Prod.mkHom (G.map (ιC.map f₁)) (𝟙 (ιD.obj L)) ≫ Prod.mkHom (𝟙 _) (ιD.map f₂) := by
    ext <;> simp
  have e₂ : Prod.mkHom (ιC.map f₁) (F.map (ιD.map f₂)) =
      Prod.mkHom (ιC.map f₁) (𝟙 (F.obj (ιD.obj L))) ≫ Prod.mkHom (𝟙 _) (F.map (ιD.map f₂)) := by
    ext <;> simp
  have h₁ := NatTrans.congr_app (α.naturality (ιC.map f₁)) (ιD.obj L)
  have h₂ := (α.app (ιC.obj M')).naturality (ιD.map f₂)
  dsimp at h₁ h₂
  rw [e₁, e₂, T_D.map_comp, T_C.map_comp, G.map_comp, Category.assoc, h₂,
    ← Category.assoc, h₁, Category.assoc]

end CategoryTheory.Functor
