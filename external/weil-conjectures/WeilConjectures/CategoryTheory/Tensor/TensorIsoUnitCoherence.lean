/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Tensor compatibility of invertible comparisons forces unit compatibility -/
@[expose] public section
set_option autoImplicit false
open CategoryTheory MonoidalCategory
namespace CategoryTheory

/-- An invertible tensor-compatible comparison between unital tensor functors preserves units.
Source: Stacks 07A4 (blueprint: lem-pur-tensor-iso-unit-coherence).
Proof: specialize tensor compatibility to the pair of units, then use naturality at
its left unitor and the left-unit axioms. Cancel the invertible tensor comparison
and the left unitor. Cancel tensoring with the invertible unit component. Finally,
tensoring on the right by an object isomorphic to the unit is faithful: conjugate
it by that isomorphism and the right unitor. -/
theorem tensorIso_preserves_unit
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F G : C ⥤ D) (a : F ≅ G)
    (dF : ∀ X Y : C, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
    (dG : ∀ X Y : C, G.obj (X ⊗ Y) ≅ G.obj X ⊗ G.obj Y)
    (eF : F.obj (𝟙_ C) ≅ 𝟙_ D) (eG : G.obj (𝟙_ C) ≅ 𝟙_ D)
    (hF : ∀ X, (dF (𝟙_ C) X).hom ≫ eF.hom ▷ F.obj X ≫
      (λ_ (F.obj X)).hom = F.map (λ_ X).hom)
    (hG : ∀ X, (dG (𝟙_ C) X).hom ≫ eG.hom ▷ G.obj X ≫
      (λ_ (G.obj X)).hom = G.map (λ_ X).hom)
    (hc : ∀ X Y, a.hom.app (X ⊗ Y) ≫ (dG X Y).hom =
      (dF X Y).hom ≫ (a.hom.app X ⊗ₘ a.hom.app Y)) :
    a.hom.app (𝟙_ C) ≫ eG.hom = eF.hom := by
  let I := 𝟙_ C
  have hn := a.hom.naturality (λ_ I).hom
  rw [← hF, ← hG] at hn
  simp only [Category.assoc] at hn
  rw [reassoc_of% (hc _ _)] at hn
  have hn' := (cancel_epi (dF I I).hom).1 hn
  have ht : eF.hom ▷ F.obj I =
      (a.hom.app I ≫ eG.hom) ▷ F.obj I := by
    have hh : eF.hom ▷ F.obj I ≫ (𝟙_ D ◁ a.hom.app I) =
        (a.hom.app I ≫ eG.hom) ▷ F.obj I ≫ (𝟙_ D ◁ a.hom.app I) := by
      apply (cancel_mono (λ_ (G.obj I)).hom).1
      rw [Category.assoc, leftUnitor_naturality]
      rw [comp_whiskerRight]
      simp only [Category.assoc]
      rw [← whisker_exchange_assoc, ← tensorHom_def_assoc]
      exact hn'
    exact (cancel_mono (𝟙_ D ◁ a.hom.app I)).1 hh
  apply (cancel_epi (F.obj I ◁ eF.hom ≫ (ρ_ (F.obj I)).hom)).1
  have hh := congrArg (fun z ↦ z ≫ (𝟙_ D ◁ eF.hom) ≫ (ρ_ (𝟙_ D)).hom) ht
  simpa only [Category.assoc, ← whisker_exchange_assoc, rightUnitor_naturality] using hh.symm

end CategoryTheory
