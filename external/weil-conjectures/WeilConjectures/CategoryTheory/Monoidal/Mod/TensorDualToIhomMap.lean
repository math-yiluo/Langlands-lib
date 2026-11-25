/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorDualToIhom

/-!
# `X ⊗_A M^∨ ⟶ Hom_A(M, X)` and monoidal functors

Let `G : C ⥤ D` be a lax monoidal functor with invertible tensor comparisons, compatible with the
symmetries, and `ρ : B ⟶ G A` a monoid morphism, inducing the functor `F` on modules
(`CategoryTheory.Mod.mapModComap`). Suppose given comparison morphisms
`F Hom_A(M, N) ⟶ Hom_B(F M, F N)` compatible with the evaluations, and a comparison
`F M^∨ ⟶ (F M)^∨` compatible with the evaluations up to a morphism `u : G A ⟶ B` with
`u ≫ ρ = 𝟙`. Then `F` carries `X ⊗_A M^∨ ⟶ Hom_A(M, X)` to `F X ⊗_B (F M)^∨ ⟶ Hom_B(F M, F X)`
up to these comparisons and the comparison `F (X ⊗_A M^∨) ≅ F X ⊗_B F M^∨`
(`CategoryTheory.Mod.tensorLeftCompMapModComapIso_inv_app_map_tensorDualToIhom`).
-/

@[expose] public section

universe v u v' u'

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal

open scoped Obj

namespace CategoryTheory.Mod

section Generic

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (G : C ⥤ D) [G.LaxMonoidal]

/-- The computation behind
`CategoryTheory.Mod.tensorLeftCompMapModComapIso_inv_app_map_tensorDualToIhom`,
for arbitrary morphisms. -/
lemma μ_whiskerRight_μ_map_associator_whiskerLeft {X Y M A : C} {B Y' : D} (e : Y ⊗ M ⟶ A)
    (r : X ⊗ A ⟶ X) (u : G.obj A ⟶ B) (δ : G.obj Y ⟶ Y') (e' : Y' ⊗ G.obj M ⟶ B)
    (r' : G.obj X ⊗ B ⟶ G.obj X) (hδ : δ ▷ G.obj M ≫ e' = μ G Y M ≫ G.map e ≫ u)
    (hr : μ G X A ≫ G.map r = G.obj X ◁ u ≫ r') :
    μ G X Y ▷ G.obj M ≫ μ G (X ⊗ Y) M ≫ G.map ((α_ X Y M).hom ≫ X ◁ e ≫ r) =
      (G.obj X ◁ δ) ▷ G.obj M ≫ (α_ _ _ _).hom ≫ G.obj X ◁ e' ≫ r' := by
  rw [associator_naturality_middle_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, hδ,
    G.map_comp, G.map_comp, associativity_assoc, ← μ_natural_right_assoc, hr]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- `G` carries `x ⊗ a ↦ a x` to `y ⊗ b ↦ ρ(b) y`, up to `u : G A ⟶ B` with `u ≫ ρ = 𝟙`. -/
lemma μ_map_braiding_comp {A : C} {B : D} (X : C) (a : A ⊗ X ⟶ X) (ρ : B ⟶ G.obj A)
    (u : G.obj A ⟶ B) (hu : u ≫ ρ = 𝟙 _) [BraidedCategory C] [BraidedCategory D]
    (hβ : ∀ X Y : C, μ G X Y ≫ G.map (β_ X Y).hom = (β_ (G.obj X) (G.obj Y)).hom ≫ μ G Y X) :
    μ G X A ≫ G.map ((β_ X A).hom ≫ a) =
      G.obj X ◁ u ≫ (β_ (G.obj X) B).hom ≫ ρ ▷ G.obj X ≫ μ G A X ≫ G.map a := by
  rw [BraidedCategory.braiding_naturality_right_assoc, ← comp_whiskerRight_assoc, hu,
    id_whiskerRight, Category.id_comp, G.map_comp, ← Category.assoc, hβ, Category.assoc]

/-- The left-hand side of
`CategoryTheory.Mod.tensorLeftCompMapModComapIso_inv_app_map_tensorDualToIhom`,
for arbitrary morphisms. -/
lemma comp_map_comp_whiskerRight_comp {X Y M S H N : C} {T H' : D}
    (t : X ⊗ Y ⟶ S) (c : S ⟶ H) (ev : H ⊗ M ⟶ N) (t' : G.obj X ⊗ G.obj Y ⟶ T)
    (k : T ⟶ G.obj S) (ψ : G.obj H ⟶ H') (ev' : H' ⊗ G.obj M ⟶ G.obj N)
    (ht : t' ≫ k = μ G X Y ≫ G.map t) (hψ : ψ ▷ G.obj M ≫ ev' = μ G H M ≫ G.map ev) :
    (t' ≫ k ≫ G.map c ≫ ψ) ▷ G.obj M ≫ ev' =
      μ G X Y ▷ G.obj M ≫ μ G (X ⊗ Y) M ≫ G.map ((t ≫ c) ▷ M ≫ ev) := by
  rw [reassoc_of% ht]
  simp only [comp_whiskerRight, Category.assoc, hψ, μ_natural_left_assoc, Functor.map_comp]

end Generic

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]
  [SymmetricCategory C] [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C]
  [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {B : D} [MonObj B]
  [SymmetricCategory D] [IsCommMonObj B] [Abelian D] [MonoidalPreadditive D]
  [IsGrothendieckAbelian.{v'} D]
  [∀ X : D, PreservesColimitsOfSize.{v', v'} (MonoidalCategory.tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{v', v'} (MonoidalCategory.tensorRight X)]
  {G : C ⥤ D} [G.LaxMonoidal] [∀ X Y : C, IsIso (μ G X Y)]
  (ρ : B ⟶ G.obj A) [IsMonHom ρ] [IsIso ρ]

omit [Abelian C] [MonoidalPreadditive C] [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]
  [Abelian D] [MonoidalPreadditive D] [IsGrothendieckAbelian.{v'} D]
  [∀ X : D, PreservesColimitsOfSize.{v', v'} (MonoidalCategory.tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{v', v'} (MonoidalCategory.tensorRight X)]
  [∀ X Y : C, IsIso (μ G X Y)] [IsCommMonObj A] [IsCommMonObj B] [IsIso ρ] in
/-- `G` carries the right action to the right action, up to `u : G A ⟶ B` with `u ≫ ρ = 𝟙`. -/
lemma μ_map_rightAct
    (hβ : ∀ X Y : C, μ G X Y ≫ G.map (β_ X Y).hom = (β_ (G.obj X) (G.obj Y)).hom ≫ μ G Y X)
    (X : Mod C A) (u : G.obj A ⟶ B) (hu : u ≫ ρ = 𝟙 _) :
    μ G X.X A ≫ G.map (rightAct X) = G.obj X.X ◁ u ≫ rightAct ((mapModComap ρ).obj X) := by
  exact μ_map_braiding_comp G X.X (act X.X) ρ u hu hβ

variable [PreservesColimitsOfShape WalkingParallelPair (mapModComap ρ)]

omit [MonoidalPreadditive C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]
  [MonoidalPreadditive D]
  [∀ X : D, PreservesColimitsOfSize.{v', v'} (MonoidalCategory.tensorRight X)] in
/-- The quotient map `F X ⊗ F D ⟶ F X ⊗_B F D ≅ F (X ⊗_A D)` is `G` of the quotient map. -/
@[reassoc]
lemma tensorπ_tensorLeftCompMapModComapIso_inv_app
    (hβ : ∀ X Y : C, μ G X Y ≫ G.map (β_ X Y).hom = (β_ (G.obj X) (G.obj Y)).hom ≫ μ G Y X)
    (X M : Mod C A) :
    tensorπ ((mapModComap ρ).obj X) ((mapModComap ρ).obj M) ≫
        ((tensorLeftCompMapModComapIso ρ hβ M).inv.app X).hom =
      μ G X.X M.X ≫ G.map (tensorπ X M) := by
  rw [← cancel_epi (inv (μ G X.X M.X)), IsIso.inv_hom_id_assoc]
  erw [← map_tensorπ_comp_tensorLeftCompMapModComapIso_hom_assoc ρ hβ X M]
  rw [← Mod.comp_hom', Iso.hom_inv_id_app, Mod.id_hom']
  exact Category.comp_id _

/-- **`F` carries `X ⊗_A M^∨ ⟶ Hom_A(M, X)` to `F X ⊗_B (F M)^∨ ⟶ Hom_B(F M, F X)`**, up to the
comparison `F (X ⊗_A M^∨) ≅ F X ⊗_B F M^∨`, a comparison `ψ : F Hom_A(M, X) ⟶ Hom_B(F M, F X)`
compatible with the evaluations, and a comparison `δ : F M^∨ ⟶ (F M)^∨` compatible with the
evaluations up to `u : G A ⟶ B` with `u ≫ ρ = 𝟙`. -/
lemma tensorLeftCompMapModComapIso_inv_app_map_tensorDualToIhom
    (hβ : ∀ X Y : C, μ G X Y ≫ G.map (β_ X Y).hom = (β_ (G.obj X) (G.obj Y)).hom ≫ μ G Y X)
    (M X : Mod C A)
    (ψ : (mapModComap ρ).obj ((ihom M).obj X) ⟶
      (ihom ((mapModComap ρ).obj M)).obj ((mapModComap ρ).obj X))
    (hψ : ψ.hom ▷ ((mapModComap ρ).obj M).X ≫
      evaluation ((mapModComap ρ).obj M) ((mapModComap ρ).obj X) =
      μ G _ M.X ≫ G.map (evaluation M X))
    (δ : (mapModComap ρ).obj ((ihom M).obj (regular A)) ⟶
      (ihom ((mapModComap ρ).obj M)).obj (regular B))
    (u : G.obj A ⟶ B) (hu : u ≫ ρ = 𝟙 _)
    (hδ : δ.hom ▷ ((mapModComap ρ).obj M).X ≫ evaluation ((mapModComap ρ).obj M) (regular B) =
      μ G _ M.X ≫ G.map (evaluation M (regular A)) ≫ u) :
    (tensorLeftCompMapModComapIso ρ hβ _).inv.app X ≫ (mapModComap ρ).map (tensorDualToIhom M X) ≫
        ψ = (tensorLeftMap δ).app _ ≫ tensorDualToIhom _ _ := by
  refine tensorLeft_ihom_hom_ext ?_
  have hL : (tensorπ ((mapModComap ρ).obj X) ((mapModComap ρ).obj ((ihom M).obj (regular A))) ≫
      ((tensorLeftCompMapModComapIso ρ hβ _).inv.app X ≫
        (mapModComap ρ).map (tensorDualToIhom M X) ≫ ψ).hom) ▷ ((mapModComap ρ).obj M).X ≫
      evaluation ((mapModComap ρ).obj M) ((mapModComap ρ).obj X) =
      μ G X.X _ ▷ G.obj M.X ≫ μ G _ M.X ≫ G.map (tensorDualToIhomAux M X) := by
    rw [← tensorπ_tensorDualToIhom_evaluation]
    exact comp_map_comp_whiskerRight_comp G _ _ _ _ _ ψ.hom _
      (tensorπ_tensorLeftCompMapModComapIso_inv_app ρ hβ X _) hψ
  have hR : (tensorπ ((mapModComap ρ).obj X) ((mapModComap ρ).obj ((ihom M).obj (regular A))) ≫
      ((tensorLeftMap δ).app _ ≫ tensorDualToIhom _ _).hom) ▷ ((mapModComap ρ).obj M).X ≫
      evaluation ((mapModComap ρ).obj M) ((mapModComap ρ).obj X) =
      (((mapModComap ρ).obj X).X ◁ δ.hom) ▷ ((mapModComap ρ).obj M).X ≫
        tensorDualToIhomAux _ _ := by
    rw [Mod.comp_hom', tensorπ_tensorLeftMap_assoc, comp_whiskerRight_assoc,
      tensorπ_tensorDualToIhom_evaluation]
  rw [hL, hR]
  exact μ_whiskerRight_μ_map_associator_whiskerLeft G (evaluation M (regular A)) (rightAct X) u
    δ.hom _ (rightAct ((mapModComap ρ).obj X)) hδ (μ_map_rightAct ρ hβ X u hu)

end CategoryTheory.Mod
