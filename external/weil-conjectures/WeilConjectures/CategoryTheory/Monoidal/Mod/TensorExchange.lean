/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Transpose

/-!
# Monoidal exchange isomorphisms and tensor products of modules

Let `G : C ⥤ D`, `F : C ⥤ C` and `F' : D ⥤ D` be lax monoidal functors with invertible tensor
comparisons, inducing functors on modules over commutative monoids along monoid morphisms
`ρ : B ⟶ G A`, `σ : A ⟶ F A` and `σ' : B ⟶ F' B`. A monoidal natural transformation
`θ : G ⋙ F' ⟶ F ⋙ G`, together with morphisms of modules `E M : F' (G M) ⟶ G (F M)` lifting it,
is compatible with the comparisons `G (P ⊗_A M) ≅ G P ⊗_B G M`
(`CategoryTheory.Mod.tensorLeftCompMapModComapIso`) of the three functors
(`CategoryTheory.Mod.tensorLeftCompMapModComapIso_exchange`).
-/

@[expose] public section

universe v u v' u'

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal

namespace CategoryTheory.Mod

open scoped Obj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]
  [BraidedCategory C] [IsCommMonObj A] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {B : D} [MonObj B]
  [BraidedCategory D] [IsCommMonObj B] [Abelian D] [IsGrothendieckAbelian.{v'} D]
  [∀ X : D, PreservesColimitsOfSize.{v', v'} (MonoidalCategory.tensorLeft X)]
  {G : C ⥤ D} [G.LaxMonoidal] [∀ X Y : C, IsIso (μ G X Y)]
  (ρ : B ⟶ G.obj A) [IsMonHom ρ] [IsIso ρ]
  [PreservesColimitsOfShape WalkingParallelPair (mapModComap ρ)]

omit [IsCommMonObj B] [Abelian D] [IsGrothendieckAbelian.{v'} D]
  [∀ X : D, PreservesColimitsOfSize.{v', v'} (MonoidalCategory.tensorLeft X)] in
/-- Two morphisms out of `P ⊗_A M` agreeing on `P ⊗ M` are equal. -/
lemma tensorLeft_obj_hom_ext' {P M N : Mod C A} {f g : (tensorLeft M).obj P ⟶ N}
    (h : tensorπ P M ≫ f.hom = tensorπ P M ≫ g.hom) : f = g := by
  have h₁ : colimit.ι ((tensorLeftDiagram A M).flip.obj P) WalkingParallelPair.one ≫ f =
      colimit.ι ((tensorLeftDiagram A M).flip.obj P) WalkingParallelPair.one ≫ g :=
    Mod.hom_ext _ _ h
  refine colimit.hom_ext fun j ↦ ?_
  cases j
  · rw [← colimit.w ((tensorLeftDiagram A M).flip.obj P) WalkingParallelPairHom.left,
      Category.assoc, Category.assoc, h₁]
  · exact h₁

/-- The comparison `G (P ⊗_A M) ≅ G P ⊗_B G M` on the quotient maps. -/
@[reassoc]
lemma μ_map_tensorπ_comp_tensorLeftCompMapModComapIso_hom
    (hβ : ∀ X Y : C, μ G X Y ≫ G.map (β_ X Y).hom = (β_ (G.obj X) (G.obj Y)).hom ≫ μ G Y X)
    (P M : Mod C A) :
    μ G P.X M.X ≫ G.map (tensorπ P M) ≫ ((tensorLeftCompMapModComapIso ρ hβ M).hom.app P).hom =
      tensorπ ((mapModComap ρ).obj P) ((mapModComap ρ).obj M) := by
  rw [map_tensorπ_comp_tensorLeftCompMapModComapIso_hom, IsIso.hom_inv_id_assoc]

variable {F : C ⥤ C} [F.LaxMonoidal] [∀ X Y : C, IsIso (μ F X Y)]
  (σ : A ⟶ F.obj A) [IsMonHom σ] [IsIso σ]
  [PreservesColimitsOfShape WalkingParallelPair (mapModComap σ)]
  {F' : D ⥤ D} [F'.LaxMonoidal] [∀ X Y : D, IsIso (μ F' X Y)]
  (σ' : B ⟶ F'.obj B) [IsMonHom σ'] [IsIso σ']
  [PreservesColimitsOfShape WalkingParallelPair (mapModComap σ')]

/-- Two morphisms out of `F' (G (P ⊗_A M))` agreeing on `F' (G P) ⊗ F' (G M)` are equal. -/
lemma mapModComap_mapModComap_tensorLeft_hom_ext
    (hβ : ∀ X Y : C, μ G X Y ≫ G.map (β_ X Y).hom = (β_ (G.obj X) (G.obj Y)).hom ≫ μ G Y X)
    (hβF' : ∀ X Y : D, μ F' X Y ≫ F'.map (β_ X Y).hom =
      (β_ (F'.obj X) (F'.obj Y)).hom ≫ μ F' Y X)
    {P M : Mod C A} {N : Mod D B}
    {f₁ f₂ : (mapModComap σ').obj ((mapModComap ρ).obj ((tensorLeft M).obj P)) ⟶ N}
    (h : μ F' (G.obj P.X) (G.obj M.X) ≫ F'.map (μ G P.X M.X) ≫
        F'.map (G.map (tensorπ P M)) ≫ f₁.hom =
      μ F' (G.obj P.X) (G.obj M.X) ≫ F'.map (μ G P.X M.X) ≫
        F'.map (G.map (tensorπ P M)) ≫ f₂.hom) :
    f₁ = f₂ := by
  let Φ := (mapModComap σ').mapIso ((tensorLeftCompMapModComapIso ρ hβ M).app P) ≪≫
    (tensorLeftCompMapModComapIso σ' hβF' ((mapModComap ρ).obj M)).app ((mapModComap ρ).obj P)
  have hΦ : μ F' (G.obj P.X) (G.obj M.X) ≫ F'.map (μ G P.X M.X) ≫
      F'.map (G.map (tensorπ P M)) ≫ Φ.hom.hom =
      tensorπ ((mapModComap σ').obj ((mapModComap ρ).obj P))
        ((mapModComap σ').obj ((mapModComap ρ).obj M)) := by
    simp only [Φ, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Mod.comp_hom']
    erw [← F'.map_comp_assoc, ← F'.map_comp_assoc, Category.assoc,
      μ_map_tensorπ_comp_tensorLeftCompMapModComapIso_hom ρ hβ P M]
    exact μ_map_tensorπ_comp_tensorLeftCompMapModComapIso_hom σ' hβF' ((mapModComap ρ).obj P)
      ((mapModComap ρ).obj M)
  rw [← Φ.hom_inv_id_assoc f₁, ← Φ.hom_inv_id_assoc f₂]
  congr 1
  refine tensorLeft_obj_hom_ext' (P := (mapModComap σ').obj ((mapModComap ρ).obj P))
    (M := (mapModComap σ').obj ((mapModComap ρ).obj M)) ?_
  rw [← hΦ, Mod.comp_hom', Mod.comp_hom']
  simp only [Category.assoc]
  have hh : Φ.hom.hom ≫ Φ.inv.hom = 𝟙 _ := by
    rw [← Mod.comp_hom', Φ.hom_inv_id]
    rfl
  rw [reassoc_of% hh, reassoc_of% hh]
  exact h

/-- **Exchange isomorphisms are compatible with tensor products of modules.** A monoidal
natural transformation `θ : G ⋙ F' ⟶ F ⋙ G`, lifted to morphisms of modules
`E M : F' (G M) ⟶ G (F M)`, is compatible with the comparisons `G (P ⊗ M) ≅ G P ⊗ G M`,
`F (P ⊗ M) ≅ F P ⊗ F M` and `F' (P ⊗ M) ≅ F' P ⊗ F' M`. -/
lemma tensorLeftCompMapModComapIso_exchange
    (hβ : ∀ X Y : C, μ G X Y ≫ G.map (β_ X Y).hom = (β_ (G.obj X) (G.obj Y)).hom ≫ μ G Y X)
    (hβF : ∀ X Y : C, μ F X Y ≫ F.map (β_ X Y).hom = (β_ (F.obj X) (F.obj Y)).hom ≫ μ F Y X)
    (hβF' : ∀ X Y : D, μ F' X Y ≫ F'.map (β_ X Y).hom =
      (β_ (F'.obj X) (F'.obj Y)).hom ≫ μ F' Y X)
    (θ : G ⋙ F' ⟶ F ⋙ G)
    (hθ : ∀ X Y : C, μ F' (G.obj X) (G.obj Y) ≫ F'.map (μ G X Y) ≫ θ.app (X ⊗ Y) =
      (θ.app X ⊗ₘ θ.app Y) ≫ μ G (F.obj X) (F.obj Y) ≫ G.map (μ F X Y))
    (E : ∀ M : Mod C A, (mapModComap σ').obj ((mapModComap ρ).obj M) ⟶
      (mapModComap ρ).obj ((mapModComap σ).obj M))
    (P M : Mod C A) (hEP : (E P).hom = θ.app P.X) (hEM : (E M).hom = θ.app M.X)
    (hEPM : (E ((tensorLeft M).obj P)).hom = θ.app ((tensorLeft M).obj P).X) :
    (mapModComap σ').map ((tensorLeftCompMapModComapIso ρ hβ M).hom.app P) ≫
        (tensorLeftCompMapModComapIso σ' hβF' ((mapModComap ρ).obj M)).hom.app
          ((mapModComap ρ).obj P) ≫
        (tensorLeftMap (E M)).app _ ≫ (tensorLeft _).map (E P) =
      E ((tensorLeft M).obj P) ≫
        (mapModComap ρ).map ((tensorLeftCompMapModComapIso σ hβF M).hom.app P) ≫
        (tensorLeftCompMapModComapIso ρ hβ ((mapModComap σ).obj M)).hom.app
          ((mapModComap σ).obj P) := by
  refine mapModComap_mapModComap_tensorLeft_hom_ext ρ σ' hβ hβF' ?_
  have n₁ : F'.map (G.map (tensorπ P M)) ≫ (E ((tensorLeft M).obj P)).hom =
      θ.app (P.X ⊗ M.X) ≫ G.map (F.map (tensorπ P M)) := by
    rw [hEPM]
    exact θ.naturality (tensorπ P M)
  have m := hθ P.X M.X
  have k : μ G (F.obj P.X) (F.obj M.X) ≫ G.map (μ F P.X M.X) ≫
      G.map (F.map (tensorπ P M)) ≫ G.map ((tensorLeftCompMapModComapIso σ hβF M).hom.app P).hom ≫
      ((tensorLeftCompMapModComapIso ρ hβ ((mapModComap σ).obj M)).hom.app
        ((mapModComap σ).obj P)).hom =
      tensorπ ((mapModComap ρ).obj ((mapModComap σ).obj P))
        ((mapModComap ρ).obj ((mapModComap σ).obj M)) := by
    erw [← G.map_comp_assoc, ← G.map_comp_assoc, Category.assoc,
      μ_map_tensorπ_comp_tensorLeftCompMapModComapIso_hom σ hβF P M]
    exact μ_map_tensorπ_comp_tensorLeftCompMapModComapIso_hom ρ hβ ((mapModComap σ).obj P)
      ((mapModComap σ).obj M)
  have L : μ F' (G.obj P.X) (G.obj M.X) ≫ F'.map (μ G P.X M.X) ≫
      F'.map (G.map (tensorπ P M)) ≫
      F'.map ((tensorLeftCompMapModComapIso ρ hβ M).hom.app P).hom ≫
      ((tensorLeftCompMapModComapIso σ' hβF' ((mapModComap ρ).obj M)).hom.app
          ((mapModComap ρ).obj P)).hom =
      tensorπ ((mapModComap σ').obj ((mapModComap ρ).obj P))
        ((mapModComap σ').obj ((mapModComap ρ).obj M)) := by
    erw [← F'.map_comp_assoc, ← F'.map_comp_assoc, Category.assoc,
      μ_map_tensorπ_comp_tensorLeftCompMapModComapIso_hom ρ hβ P M]
    exact μ_map_tensorπ_comp_tensorLeftCompMapModComapIso_hom σ' hβF' ((mapModComap ρ).obj P)
      ((mapModComap ρ).obj M)
  simp only [Mod.comp_hom']
  erw [reassoc_of% L, reassoc_of% n₁, reassoc_of% m, k, tensorπ_tensorLeftMap_assoc,
    tensorπ_map, ← tensorHom_def'_assoc, hEP, hEM]

/-- `CategoryTheory.Mod.tensorLeftCompMapModComapIso_exchange` for a monoidal natural
transformation `θ`. -/
lemma tensorLeftCompMapModComapIso_exchange_of_isMonoidal
    (hβ : ∀ X Y : C, μ G X Y ≫ G.map (β_ X Y).hom = (β_ (G.obj X) (G.obj Y)).hom ≫ μ G Y X)
    (hβF : ∀ X Y : C, μ F X Y ≫ F.map (β_ X Y).hom = (β_ (F.obj X) (F.obj Y)).hom ≫ μ F Y X)
    (hβF' : ∀ X Y : D, μ F' X Y ≫ F'.map (β_ X Y).hom =
      (β_ (F'.obj X) (F'.obj Y)).hom ≫ μ F' Y X)
    (θ : G ⋙ F' ⟶ F ⋙ G) [NatTrans.IsMonoidal θ]
    (E : ∀ M : Mod C A, (mapModComap σ').obj ((mapModComap ρ).obj M) ⟶
      (mapModComap ρ).obj ((mapModComap σ).obj M))
    (P M : Mod C A) (hEP : (E P).hom = θ.app P.X) (hEM : (E M).hom = θ.app M.X)
    (hEPM : (E ((tensorLeft M).obj P)).hom = θ.app ((tensorLeft M).obj P).X) :
    (mapModComap σ').map ((tensorLeftCompMapModComapIso ρ hβ M).hom.app P) ≫
        (tensorLeftCompMapModComapIso σ' hβF' ((mapModComap ρ).obj M)).hom.app
          ((mapModComap ρ).obj P) ≫
        (tensorLeftMap (E M)).app _ ≫ (tensorLeft _).map (E P) =
      E ((tensorLeft M).obj P) ≫
        (mapModComap ρ).map ((tensorLeftCompMapModComapIso σ hβF M).hom.app P) ≫
        (tensorLeftCompMapModComapIso ρ hβ ((mapModComap σ).obj M)).hom.app
          ((mapModComap σ).obj P) :=
  tensorLeftCompMapModComapIso_exchange ρ σ σ' hβ hβF hβF' θ
    (fun X Y ↦ by simpa only [Functor.LaxMonoidal.comp_μ, Category.assoc] using
      NatTrans.IsMonoidal.tensor (τ := θ) X Y) E P M hEP hEM hEPM

end CategoryTheory.Mod
