/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Transport
import all WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorAssociatorRepresentatives

/-! # Tensor comparisons for transported monoidal structures

Source: Mathlib monoidal transport and functor associativity; explicit model comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace CategoryTheory

/-- Counit tensor comparison for a monoidal structure transported along an equivalence.
Source: Mathlib monoidal transport, the counit of the transported equivalence.
(blueprint: lem-sf-transported-tensor-comparison). -/
def transportedTensorComparison {C D : Type*} [Category C] [Category D]
    [MonoidalCategory D] (E : C ≌ D) :
    letI := Monoidal.transport E.symm
    MonoidalCategory.tensor C ⋙ E.functor ≅
      E.functor.prod E.functor ⋙ MonoidalCategory.tensor D := by
  letI := Monoidal.transport E.symm
  exact NatIso.ofComponents (fun XY ↦ E.counitIso.app (E.functor.obj XY.1 ⊗
    E.functor.obj XY.2)) (fun f ↦ by
      exact E.counitIso.hom.naturality (E.functor.map f.1 ⊗ₘ E.functor.map f.2))

set_option linter.style.haveILetI false in
/-- The transported counit comparison respects associativity.
Source: Mathlib Functor.OplaxMonoidal.associativity.
(blueprint: lem-sf-transported-tensor-comparison). -/
theorem transportedTensorComparison_associativity
    {C D : Type*} [Category C] [Category D] [MonoidalCategory D] (E : C ≌ D)
    (X Y Z : C) :
    letI := Monoidal.transport E.symm
    let μ := transportedTensorComparison E
    μ.hom.app (X ⊗ Y, Z) ≫ (μ.hom.app (X, Y) ▷ E.functor.obj Z) ≫
        (α_ (E.functor.obj X) (E.functor.obj Y) (E.functor.obj Z)).hom =
      E.functor.map (α_ X Y Z).hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
        (E.functor.obj X ◁ μ.hom.app (Y, Z)) := by
  letI := Monoidal.transport E.symm
  letI : E.functor.Monoidal :=
    inferInstanceAs (Monoidal.equivalenceTransported E.symm).inverse.Monoidal
  exact Functor.OplaxMonoidal.associativity E.functor X Y Z

/-- Faithful monoidal comparison detects an associator equation between explicit models.
Source: elementary cancellation and associator naturality, used in native tensor transport.
(blueprint: lem-sf-transported-tensor-comparison). -/
theorem associator_of_model_comparison
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Faithful]
    (μ : MonoidalCategory.tensor C ⋙ F ≅ F.prod F ⋙ MonoidalCategory.tensor D)
    {X Y Z V W : C} {X' Y' Z' V' W' : D}
    (l : V ≅ (X ⊗ Y) ⊗ Z) (r : W ≅ X ⊗ (Y ⊗ Z)) (a : V ⟶ W)
    (l' : V' ⟶ (X' ⊗ Y') ⊗ Z') (r' : W' ⟶ X' ⊗ (Y' ⊗ Z')) (a' : V' ⟶ W')
    (eX : F.obj X ≅ X') (eY : F.obj Y ≅ Y') (eZ : F.obj Z ≅ Z')
    (eV : F.obj V ⟶ V') (eW : F.obj W ⟶ W')
    (hA : l' ≫ (α_ X' Y' Z').hom = a' ≫ r')
    (hL : F.map l.hom ≫ μ.hom.app (X ⊗ Y, Z) ≫
      (μ.hom.app (X, Y) ▷ F.obj Z) ≫ ((eX.hom ⊗ₘ eY.hom) ⊗ₘ eZ.hom) = eV ≫ l')
    (hR : F.map r.hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
      (F.obj X ◁ μ.hom.app (Y, Z)) ≫ (eX.hom ⊗ₘ (eY.hom ⊗ₘ eZ.hom)) = eW ≫ r')
    (hC : F.map a ≫ eW = eV ≫ a')
    (hμ : μ.hom.app (X ⊗ Y, Z) ≫ (μ.hom.app (X, Y) ▷ F.obj Z) ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
      F.map (α_ X Y Z).hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
        (F.obj X ◁ μ.hom.app (Y, Z))) :
    l.hom ≫ (α_ X Y Z).hom = a ≫ r.hom := by
  apply F.map_injective
  apply (cancel_mono (μ.hom.app (X, Y ⊗ Z) ≫
    (F.obj X ◁ μ.hom.app (Y, Z)) ≫ (eX.hom ⊗ₘ (eY.hom ⊗ₘ eZ.hom)))).1
  simp only [Functor.map_comp, Category.assoc]
  calc
    _ = F.map l.hom ≫ μ.hom.app (X ⊗ Y, Z) ≫
        (μ.hom.app (X, Y) ▷ F.obj Z) ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
        (eX.hom ⊗ₘ (eY.hom ⊗ₘ eZ.hom)) := by rw [reassoc_of% hμ]
    _ = F.map l.hom ≫ μ.hom.app (X ⊗ Y, Z) ≫
        (μ.hom.app (X, Y) ▷ F.obj Z) ≫
        ((eX.hom ⊗ₘ eY.hom) ⊗ₘ eZ.hom) ≫ (α_ X' Y' Z').hom := by
      rw [associator_naturality]
      rfl
    _ = eV ≫ l' ≫ (α_ X' Y' Z').hom := by rw [reassoc_of% hL]
    _ = eV ≫ a' ≫ r' := by rw [hA]
    _ = F.map a ≫ eW ≫ r' := by rw [reassoc_of% hC]
    _ = _ := by rw [hR]

/-- Naturality of a localization factor carries a model square through localization.
Source: naturality of a natural isomorphism and functoriality of composition.
(blueprint: lem-sf-transported-tensor-comparison). -/
theorem localizationModel_square
    {C D B A : Type*} [Category C] [Category D] [Category B] [Category A]
    (q : C ⥤ B) (p : D ⥤ A) (F : B ⥤ A) (V : C ⥤ D)
    (τ : q ⋙ F ≅ V ⋙ p)
    {L R : C} {L' R' : D} (a : L ⟶ R)
    (l : V.obj L ⟶ L') (r : V.obj R ⟶ R') (a' : L' ⟶ R')
    (h : V.map a ≫ r = l ≫ a') :
    F.map (q.map a) ≫ τ.hom.app R ≫ p.map r =
      (τ.hom.app L ≫ p.map l) ≫ p.map a' := by
  have hn := τ.hom.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← p.map_comp, h, p.map_comp, Category.assoc]

/-- The preimage of a conjugated associator satisfies its defining model square.
Source: full faithfulness and cancellation of the right model isomorphism.
(blueprint: lem-sf-transported-tensor-comparison). -/
theorem preimageAssociator_square
    {C D : Type*} [Category C] [Category D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Full] [F.Faithful]
    {L R : C} {X Y Z : D}
    (l : F.obj L ≅ (X ⊗ Y) ⊗ Z) (r : F.obj R ≅ X ⊗ (Y ⊗ Z)) :
    F.map (F.preimageIso (l ≪≫ α_ X Y Z ≪≫ r.symm)).hom ≫ r.hom =
      l.hom ≫ (α_ X Y Z).hom := by
  simp only [Functor.preimageIso_hom, Functor.map_preimage, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Paste two binary model squares and move the inner comparison through localization.
Source: tensor-comparison naturality and functoriality of the tensor.
(blueprint: lem-sf-transported-tensor-comparison). -/
theorem tensorModel_left_square
    {B A D : Type*} [Category B] [Category A] [Category D]
    [MonoidalCategory B] [MonoidalCategory A] [MonoidalCategory D]
    (F : B ⥤ A) (p : D ⥤ A)
    (μ : MonoidalCategory.tensor B ⋙ F ≅ F.prod F ⋙ MonoidalCategory.tensor A)
    {X Y Z V W : B} {X' Y' Z' V' W' : D}
    (i : V ⟶ X ⊗ Y) (j : W ⟶ V ⊗ Z)
    (eX : F.obj X ⟶ p.obj X') (eY : F.obj Y ⟶ p.obj Y')
    (eZ : F.obj Z ⟶ p.obj Z') (eV : F.obj V ⟶ p.obj V')
    (eW : F.obj W ⟶ p.obj W')
    (c : V' ⟶ X' ⊗ Y') (d : W' ⟶ V' ⊗ Z')
    (δ : p.obj (X' ⊗ Y') ⟶ p.obj X' ⊗ p.obj Y')
    (δ₀ : p.obj (V' ⊗ Z') ⟶ p.obj V' ⊗ p.obj Z')
    (δ₁ : p.obj ((X' ⊗ Y') ⊗ Z') ⟶ p.obj (X' ⊗ Y') ⊗ p.obj Z')
    (hi : F.map i ≫ μ.hom.app (X, Y) ≫ (eX ⊗ₘ eY) = eV ≫ p.map c ≫ δ)
    (hj : F.map j ≫ μ.hom.app (V, Z) ≫ (eV ⊗ₘ eZ) = eW ≫ p.map d ≫ δ₀)
    (hn : p.map (c ▷ Z') ≫ δ₁ = δ₀ ≫ (p.map c ▷ p.obj Z')) :
    F.map (j ≫ (i ▷ Z)) ≫ μ.hom.app (X ⊗ Y, Z) ≫
        (μ.hom.app (X, Y) ▷ F.obj Z) ≫ ((eX ⊗ₘ eY) ⊗ₘ eZ) =
      (eW ≫ p.map (d ≫ (c ▷ Z'))) ≫ (δ₁ ≫ (δ ▷ p.obj Z')) := by
  have h := RingedForgetTensorTransposition.left_square F μ i j eX eY eZ eV eW
    (p.map c ≫ δ) (p.map d ≫ δ₀) hi hj
  rw [h]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← reassoc_of% hn]
  simp only [p.map_comp, Category.assoc]

/-- The right-associated form of the binary model square calculation.
Source: tensor-comparison naturality and functoriality of the tensor.
(blueprint: lem-sf-transported-tensor-comparison). -/
theorem tensorModel_right_square
    {B A D : Type*} [Category B] [Category A] [Category D]
    [MonoidalCategory B] [MonoidalCategory A] [MonoidalCategory D]
    (F : B ⥤ A) (p : D ⥤ A)
    (μ : MonoidalCategory.tensor B ⋙ F ≅ F.prod F ⋙ MonoidalCategory.tensor A)
    {X Y Z V W : B} {X' Y' Z' V' W' : D}
    (i : V ⟶ Y ⊗ Z) (j : W ⟶ X ⊗ V)
    (eX : F.obj X ⟶ p.obj X') (eY : F.obj Y ⟶ p.obj Y')
    (eZ : F.obj Z ⟶ p.obj Z') (eV : F.obj V ⟶ p.obj V')
    (eW : F.obj W ⟶ p.obj W')
    (c : V' ⟶ Y' ⊗ Z') (d : W' ⟶ X' ⊗ V')
    (δ : p.obj (Y' ⊗ Z') ⟶ p.obj Y' ⊗ p.obj Z')
    (δ₀ : p.obj (X' ⊗ V') ⟶ p.obj X' ⊗ p.obj V')
    (δ₁ : p.obj (X' ⊗ (Y' ⊗ Z')) ⟶ p.obj X' ⊗ p.obj (Y' ⊗ Z'))
    (hi : F.map i ≫ μ.hom.app (Y, Z) ≫ (eY ⊗ₘ eZ) = eV ≫ p.map c ≫ δ)
    (hj : F.map j ≫ μ.hom.app (X, V) ≫ (eX ⊗ₘ eV) = eW ≫ p.map d ≫ δ₀)
    (hn : p.map (X' ◁ c) ≫ δ₁ = δ₀ ≫ (p.obj X' ◁ p.map c)) :
    F.map (j ≫ (X ◁ i)) ≫ μ.hom.app (X, Y ⊗ Z) ≫
        (F.obj X ◁ μ.hom.app (Y, Z)) ≫ (eX ⊗ₘ (eY ⊗ₘ eZ)) =
      (eW ≫ p.map (d ≫ (X' ◁ c))) ≫ (δ₁ ≫ (p.obj X' ◁ δ)) := by
  have h := RingedForgetTensorTransposition.right_square F μ i j eX eY eZ eV eW
    (p.map c ≫ δ) (p.map d ≫ δ₀) hi hj
  rw [h]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [← reassoc_of% hn]
  simp only [p.map_comp, Category.assoc]

/-- Invert a normalized forward representative square.
Source: cancellation of model isomorphisms and functoriality of inverses.
(blueprint: lem-sf-transported-tensor-comparison). -/
theorem inverseModel_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} {V Z Z' W : D} (i : X ≅ Y)
    (v : F.obj Y ⟶ V) (j : V ⟶ Z) (k : Z ≅ Z')
    (w : F.obj X ⟶ W) (ν : W ⟶ Z') [IsIso ν]
    (h : F.map i.hom ≫ v ≫ j = w ≫ ν ≫ k.inv) :
    F.map i.inv ≫ w = v ≫ j ≫ k.hom ≫ inv ν := by
  have hh := congrArg (fun f ↦ f ≫ k.hom) h
  simp only [Category.assoc] at hh
  have hh' := congrArg (fun f ↦ F.map i.inv ≫ f ≫ inv ν) hh
  simpa only [← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp,
    Category.assoc, IsIso.hom_inv_id, Category.comp_id] using hh'.symm

end CategoryTheory
