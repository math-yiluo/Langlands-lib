/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Reconstruction and projection identities for adjoint mates

Source: blueprint integral direct-image proof (2), its unit/counit and mate calculations.
(blueprint: lem-sp-adjunction-reconstruction-mates).
-/

@[expose] public section
set_option autoImplicit false

namespace CategoryTheory.AdjunctionReconstruction

universe v₁ v₂ v₃ v₄ v₅ v₆

variable {C : Type v₁} [Category.{v₂} C]
  {D : Type v₃} [Category.{v₄} D]
  {S : Type v₅} [Category.{v₆} S]
  {T : Type*} [Category T]

variable (L₁ : C ⥤ S) (R₁ : S ⥤ C) (L₂ : D ⥤ T) (R₂ : T ⥤ D)
  (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)

/-- The component formula for the right mate of a square.
Source: blueprint proof (2), adjunction identities
(blueprint: lem-sp-adjunction-reconstruction-mates). -/
def rightMate {F : C ⥤ D} {H : S ⥤ T}
    (β : F ⋙ L₂ ⟶ L₁ ⋙ H) : R₁ ⋙ F ⟶ H ⋙ R₂ where
  app Z := a₂.unit.app (F.obj (R₁.obj Z)) ≫
    R₂.map (β.app (R₁.obj Z) ≫ H.map (a₁.counit.app Z))
  naturality {Z W} f := by
    dsimp only [Functor.comp_map, Functor.comp_obj]
    have hu := a₂.unit.naturality (F.map (R₁.map f))
    dsimp only [Functor.id_map, Functor.comp_map] at hu
    rw [reassoc_of% hu]
    simp only [← R₂.map_comp, Category.assoc]
    congr 1
    have hb := β.naturality (R₁.map f)
    dsimp only [Functor.comp_map] at hb
    rw [← Category.assoc, hb]
    have hc := a₁.counit.naturality f
    dsimp only [Functor.comp_map, Functor.id_map] at hc
    rw [Category.assoc, ← H.map_comp, hc]
    simp only [H.map_comp]

/-- Reconstruction by the input unit is the output adjoint transpose.
Source: blueprint proof (2), adjunction identities
(blueprint: lem-sp-adjunction-reconstruction-mates). -/
theorem reconstruction_eq {F : C ⥤ D} {H : S ⥤ T}
    (β : F ⋙ L₂ ⟶ L₁ ⋙ H) (M : C) :
    F.map (a₁.unit.app M) ≫ (rightMate L₁ R₁ L₂ R₂ a₁ a₂ β).app (L₁.obj M) =
      a₂.unit.app (F.obj M) ≫ R₂.map (β.app M) := by
  dsimp only [rightMate]
  have hu := a₂.unit.naturality (F.map (a₁.unit.app M))
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [reassoc_of% hu]
  simp only [← R₂.map_comp]
  apply congrArg (fun z ↦ a₂.unit.app (F.obj M) ≫ R₂.map z)
  have hb := β.naturality (a₁.unit.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hb
  rw [← Category.assoc, hb]
  simp only [Category.assoc]
  rw [← H.map_comp, a₁.left_triangle_components]
  simp

/-- Transposing reconstruction returns the original scalar map.
Source: blueprint proof (2), adjunction identities
(blueprint: lem-sp-adjunction-reconstruction-mates). -/
theorem transpose_reconstruction {F : C ⥤ D} {H : S ⥤ T}
    (β : F ⋙ L₂ ⟶ L₁ ⋙ H) (M : C) :
    L₂.map (F.map (a₁.unit.app M) ≫
      (rightMate L₁ R₁ L₂ R₂ a₁ a₂ β).app (L₁.obj M)) ≫
        a₂.counit.app (H.obj (L₁.obj M)) = β.app M := by
  rw [reconstruction_eq L₁ R₁ L₂ R₂ a₁ a₂ β M]
  exact (a₂.homEquiv _ _).symm_apply_apply (β.app M)

/-- Reconstruction is natural in the input.
Source: blueprint proof (2), adjunction identities
(blueprint: lem-sp-adjunction-reconstruction-mates). -/
theorem reconstruction_naturality {F : C ⥤ D} {H : S ⥤ T}
    (β : F ⋙ L₂ ⟶ L₁ ⋙ H) {M N : C} (f : M ⟶ N) :
    F.map f ≫ (F.map (a₁.unit.app N) ≫
      (rightMate L₁ R₁ L₂ R₂ a₁ a₂ β).app (L₁.obj N)) =
      (F.map (a₁.unit.app M) ≫
        (rightMate L₁ R₁ L₂ R₂ a₁ a₂ β).app (L₁.obj M)) ≫
          R₂.map (H.map (L₁.map f)) := by
  rw [reconstruction_eq L₁ R₁ L₂ R₂ a₁ a₂ β M,
    reconstruction_eq L₁ R₁ L₂ R₂ a₁ a₂ β N]
  have hu := a₂.unit.naturality (F.map f)
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [reassoc_of% hu]
  simp only [← R₂.map_comp, Category.assoc]
  exact congrArg (fun z ↦ a₂.unit.app (F.obj M) ≫ R₂.map z) (β.naturality f)

/-- Finite projection of an adjunct is its finite adjoint transpose.
Source: blueprint proof (2), adjunction identities
(blueprint: lem-sp-adjunction-reconstruction-mates). -/
theorem projection_transpose {B : Type*} [Category B] (E : T ⥤ B) (R : B ⥤ D)
    (b : L₂ ⋙ E ⊣ R) {M : D} {N : T} (f : L₂.obj M ⟶ N) :
    (a₂.homEquiv _ _ f) ≫ b.homEquiv _ _ (E.map (a₂.counit.app N)) =
      b.homEquiv _ _ (E.map f) := by
  rw [← b.homEquiv_naturality_left]
  apply congrArg (b.homEquiv _ _)
  change E.map (L₂.map (a₂.homEquiv _ _ f)) ≫ E.map (a₂.counit.app N) = _
  rw [← E.map_comp]
  exact congrArg E.map ((a₂.homEquiv _ _).symm_apply_apply f)

/-- Right mates preserve pasting. Source: the mates correspondence and its pasting law.
(blueprint: lem-sp-adjunction-reconstruction-mates). -/
theorem rightMate_pasting
    {B : Type*} [Category B] {U : Type*} [Category U]
    (L₃ : B ⥤ U) (R₃ : U ⥤ B) (a₃ : L₃ ⊣ R₃)
    {F : C ⥤ D} {G : D ⥤ B} {H : S ⥤ T} {K : T ⥤ U}
    (β : F ⋙ L₂ ⟶ L₁ ⋙ H) (γ : G ⋙ L₃ ⟶ L₂ ⋙ K) (Z : S) :
    (rightMate L₁ R₁ L₃ R₃ a₁ a₃ (F := F ⋙ G) (H := H ⋙ K)
      (Functor.whiskerLeft F γ ≫ Functor.whiskerRight β K)).app Z =
      G.map ((rightMate L₁ R₁ L₂ R₂ a₁ a₂ β).app Z) ≫
        (rightMate L₂ R₂ L₃ R₃ a₂ a₃ γ).app (H.obj Z) := by
  have h := congrArg (fun t ↦ t.app Z)
    (mateEquiv_vcomp a₁ a₂ a₃
      (TwoSquare.mk _ _ _ _ β) (TwoSquare.mk _ _ _ _ γ))
  simpa [rightMate, mateEquiv, TwoSquare.hComp, TwoSquare.vComp,
    Functor.map_comp, Category.assoc] using h

/-- A final natural transformation is carried through the right mate by its right
adjoint. Source: naturality of the counit; blueprint composition of proper/open mates.
(blueprint: lem-sp-adjunction-reconstruction-mates). -/
theorem rightMate_postcompose
    {F : C ⥤ D} {H K : S ⥤ T}
    (β : F ⋙ L₂ ⟶ L₁ ⋙ H) (e : H ⟶ K) (Z : S) :
    (rightMate L₁ R₁ L₂ R₂ a₁ a₂
      (β ≫ Functor.whiskerLeft L₁ e)).app Z =
      (rightMate L₁ R₁ L₂ R₂ a₁ a₂ β).app Z ≫ R₂.map (e.app Z) := by
  dsimp only [rightMate, NatTrans.comp_app, Functor.whiskerLeft_app]
  simp only [Category.assoc, ← R₂.map_comp]
  apply congrArg (fun z ↦ a₂.unit.app _ ≫ R₂.map z)
  exact congrArg (fun z ↦ β.app _ ≫ z) (e.naturality (a₁.counit.app Z)).symm

end CategoryTheory.AdjunctionReconstruction
