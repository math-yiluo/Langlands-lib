/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Recovering the unit comparison from associative tensor comparisons

Source: factors proof (2), coefficient-unit identification; inverse-image context: Stacks 07A4.
(blueprint: lem-sp-associative-tensor-unit-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a b c d
open CategoryTheory MonoidalCategory
namespace CategoryTheory

private theorem leftUnit_of_rightUnit
    {C : Type a} [Category.{b} C] [MonoidalCategory C]
    {D : Type c} [Category.{d} D] [MonoidalCategory D]
    (F : C ⥤ D) (μ : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (ε : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (ha : ∀ A B M : C,
      F.map (α_ A B M).hom ≫ (μ.app (A, B ⊗ M)).hom ≫
          F.obj A ◁ (μ.app (B, M)).hom =
        (μ.app (A ⊗ B, M)).hom ≫ (μ.app (A, B)).hom ▷ F.obj M ≫
          (α_ (F.obj A) (F.obj B) (F.obj M)).hom)
    (hr : (μ.app (𝟙_ C, 𝟙_ C)).hom ≫ F.obj (𝟙_ C) ◁ ε.hom ≫
      (ρ_ (F.obj (𝟙_ C))).hom = F.map (ρ_ (𝟙_ C)).hom) (M : C) :
    (μ.app (𝟙_ C, M)).hom ≫ ε.hom ▷ F.obj M ≫ (λ_ (F.obj M)).hom =
      F.map (λ_ M).hom := by
  let I := 𝟙_ C
  have hnL := μ.hom.naturality (Prod.mkHom (ρ_ I).hom (𝟙 M))
  have hnR := μ.hom.naturality (Prod.mkHom (𝟙 I) (λ_ M).hom)
  change F.map ((ρ_ I).hom ⊗ₘ 𝟙 M) ≫ (μ.app (I, M)).hom =
    (μ.app (I ⊗ I, M)).hom ≫ (F.map (ρ_ I).hom ⊗ₘ F.map (𝟙 M)) at hnL
  change F.map (𝟙 I ⊗ₘ (λ_ M).hom) ≫ (μ.app (I, M)).hom =
    (μ.app (I, I ⊗ M)).hom ≫ (F.map (𝟙 I) ⊗ₘ F.map (λ_ M).hom) at hnR
  dsimp only [Functor.comp_obj, tensor_obj, Functor.prod_obj] at hnL hnR
  simp only [F.map_id, tensorHom_id, id_tensorHom] at hnL hnR
  have h : F.obj I ◁ ((μ.app (I, M)).hom ≫ ε.hom ▷ F.obj M ≫
      (λ_ (F.obj M)).hom) = F.obj I ◁ F.map (λ_ M).hom := by
    apply (cancel_epi (F.map (α_ I I M).hom ≫ (μ.app (I, I ⊗ M)).hom)).mp
    simp only [whiskerLeft_comp, Category.assoc]
    rw [reassoc_of% (ha I I M)]
    rw [← associator_naturality_middle_assoc, triangle]
    simp only [← comp_whiskerRight]
    rw [hr]
    rw [← hnL]
    rw [← triangle, F.map_comp, Category.assoc, hnR]
  have h' := congrArg
    (fun t ↦ t ≫ ε.hom ▷ F.obj M ≫ (λ_ (F.obj M)).hom) h
  dsimp only [Functor.comp_obj, tensor_obj, Functor.prod_obj] at h'
  simp only [whisker_exchange_assoc, leftUnitor_naturality] at h'
  apply (cancel_epi (ε.hom ▷ F.obj (I ⊗ M) ≫ (λ_ (F.obj (I ⊗ M))).hom)).mp
  simpa only [Category.assoc] using h'

private theorem rightUnit_of_leftUnit
    {C : Type a} [Category.{b} C] [MonoidalCategory C]
    {D : Type c} [Category.{d} D] [MonoidalCategory D]
    (F : C ⥤ D) (μ : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (ε : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (ha : ∀ A B M : C,
      F.map (α_ A B M).hom ≫ (μ.app (A, B ⊗ M)).hom ≫
          F.obj A ◁ (μ.app (B, M)).hom =
        (μ.app (A ⊗ B, M)).hom ≫ (μ.app (A, B)).hom ▷ F.obj M ≫
          (α_ (F.obj A) (F.obj B) (F.obj M)).hom)
    (hl : (μ.app (𝟙_ C, 𝟙_ C)).hom ≫ ε.hom ▷ F.obj (𝟙_ C) ≫
      (λ_ (F.obj (𝟙_ C))).hom = F.map (λ_ (𝟙_ C)).hom) (M : C) :
    (μ.app (M, 𝟙_ C)).hom ≫ F.obj M ◁ ε.hom ≫ (ρ_ (F.obj M)).hom =
      F.map (ρ_ M).hom := by
  let I := 𝟙_ C
  have hnL := μ.hom.naturality (Prod.mkHom (ρ_ M).hom (𝟙 I))
  have hnR := μ.hom.naturality (Prod.mkHom (𝟙 M) (λ_ I).hom)
  change F.map ((ρ_ M).hom ⊗ₘ 𝟙 I) ≫ (μ.app (M, I)).hom =
    (μ.app (M ⊗ I, I)).hom ≫ (F.map (ρ_ M).hom ⊗ₘ F.map (𝟙 I)) at hnL
  change F.map (𝟙 M ⊗ₘ (λ_ I).hom) ≫ (μ.app (M, I)).hom =
    (μ.app (M, I ⊗ I)).hom ≫ (F.map (𝟙 M) ⊗ₘ F.map (λ_ I).hom) at hnR
  dsimp only [Functor.comp_obj, tensor_obj, Functor.prod_obj] at hnL hnR
  simp only [F.map_id, tensorHom_id, id_tensorHom] at hnL hnR
  have h : ((μ.app (M, I)).hom ≫ F.obj M ◁ ε.hom ≫
      (ρ_ (F.obj M)).hom) ▷ F.obj I = F.map (ρ_ M).hom ▷ F.obj I := by
    apply (cancel_epi (μ.app (M ⊗ I, I)).hom).mp
    simp only [comp_whiskerRight]
    rw [← triangle, associator_naturality_middle_assoc]
    dsimp only [Functor.prod_obj]
    rw [← reassoc_of% (ha M I I)]
    simp only [← whiskerLeft_comp]
    rw [hl]
    rw [← hnR, ← F.map_comp_assoc, triangle, hnL]
  have h' := congrArg
    (fun t ↦ t ≫ F.obj M ◁ ε.hom ≫ (ρ_ (F.obj M)).hom) h
  dsimp only [Functor.comp_obj, tensor_obj, Functor.prod_obj] at h'
  simp only [← whisker_exchange_assoc, rightUnitor_naturality] at h'
  apply (cancel_epi (F.obj (M ⊗ I) ◁ ε.hom ≫ (ρ_ (F.obj (M ⊗ I))).hom)).mp
  simpa only [Category.assoc] using h'

private theorem unit_from_tensor
    {C : Type a} [Category.{b} C] [MonoidalCategory C]
    {D : Type c} [Category.{d} D] [MonoidalCategory D]
    (F : C ⥤ D) (μ : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (e : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (ha : ∀ A B M : C,
      F.map (α_ A B M).hom ≫ (μ.app (A, B ⊗ M)).hom ≫
          F.obj A ◁ (μ.app (B, M)).hom =
        (μ.app (A ⊗ B, M)).hom ≫ (μ.app (A, B)).hom ▷ F.obj M ≫
          (α_ (F.obj A) (F.obj B) (F.obj M)).hom) :
    ∃ ε : F.obj (𝟙_ C) ≅ 𝟙_ D,
      (∀ M : C, (μ.app (𝟙_ C, M)).hom ≫ (ε.hom ⊗ₘ 𝟙 (F.obj M)) ≫
        (λ_ (F.obj M)).hom = F.map (λ_ M).hom) ∧
      (∀ M : C, (μ.app (M, 𝟙_ C)).hom ≫ (𝟙 (F.obj M) ⊗ₘ ε.hom) ≫
        (ρ_ (F.obj M)).hom = F.map (ρ_ M).hom) := by
  let I := 𝟙_ C
  let t : tensorLeft (F.obj I) ≅ 𝟭 D := NatIso.ofComponents
    (fun X ↦ whiskerRightIso e X ≪≫ λ_ X) (by
      intro X Y g
      change F.obj I ◁ g ≫ e.hom ▷ Y ≫ (λ_ Y).hom =
        (e.hom ▷ X ≫ (λ_ X).hom) ≫ g
      rw [whisker_exchange_assoc, leftUnitor_naturality]
      simp only [Category.assoc])
  let ff := (Functor.FullyFaithful.id D).ofIso t.symm
  let j : (tensorLeft (F.obj I)).obj (F.obj I) ≅
      (tensorLeft (F.obj I)).obj (𝟙_ D) :=
    (μ.app (I, I)).symm ≪≫ F.mapIso (ρ_ I) ≪≫ (ρ_ (F.obj I)).symm
  let ε := ff.preimageIso j
  have hr : (μ.app (I, I)).hom ≫ F.obj I ◁ ε.hom ≫
      (ρ_ (F.obj I)).hom = F.map (ρ_ I).hom := by
    have he := ff.map_preimage j.hom
    change F.obj I ◁ ε.hom = j.hom at he
    rw [he]
    simp [j]
  have hl := leftUnit_of_rightUnit F μ ε ha hr
  refine ⟨ε, ?_, ?_⟩
  · intro M
    have h := hl M
    dsimp only [Functor.comp_obj, tensor_obj, Functor.prod_obj] at h ⊢
    simpa only [tensorHom_id] using h
  · intro M
    have h := rightUnit_of_leftUnit F μ ε ha (hl I) M
    dsimp only [Functor.comp_obj, tensor_obj, Functor.prod_obj] at h ⊢
    simpa only [id_tensorHom] using h

/-- An associative tensor comparison and preservation of the unit object determine
one unit isomorphism satisfying every right-unit equation.
Source: factors proof (2), coefficient-unit identification; elementary tensor-unit cancellation.
(blueprint: lem-sp-associative-tensor-unit-comparison).

Proof: tensoring by the image of the unit is fully faithful because that image
is isomorphic to the target unit. Pull back the composite of the inverse binary
comparison and the two right unitors to define epsilon. Its right-unit equation
at the source unit holds by construction. Associativity, naturality and the
triangle identity give all left-unit equations, then all right-unit equations.
For uniqueness use the right-unit equation at the unit, cancel its invertible
comparison and unitor, and apply faithfulness of tensoring by its image. -/
theorem tensorUnitFromAssociativity
    {C : Type a} [Category.{b} C] [MonoidalCategory C]
    {D : Type c} [Category.{d} D] [MonoidalCategory D]
    (F : C ⥤ D) (μ : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (e : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (ha : ∀ A B M : C,
      F.map (α_ A B M).hom ≫ (μ.app (A, B ⊗ M)).hom ≫
          F.obj A ◁ (μ.app (B, M)).hom =
        (μ.app (A ⊗ B, M)).hom ≫ (μ.app (A, B)).hom ▷ F.obj M ≫
          (α_ (F.obj A) (F.obj B) (F.obj M)).hom) :
    ∃! ε : F.obj (𝟙_ C) ≅ 𝟙_ D,
      ∀ M : C, F.map (ρ_ M).hom = (μ.app (M, 𝟙_ C)).hom ≫
        (𝟙 (F.obj M) ⊗ₘ ε.hom) ≫ (ρ_ (F.obj M)).hom := by
  obtain ⟨ε, _, hr⟩ := unit_from_tensor F μ e ha
  refine ⟨ε, fun M ↦ (hr M).symm, ?_⟩
  intro ε' hε'
  apply Iso.ext
  have h := (hε' (𝟙_ C)).symm.trans (hr (𝟙_ C)).symm
  dsimp only [Functor.comp_obj, Functor.prod_obj, tensor_obj] at h
  have hh : F.obj (𝟙_ C) ◁ ε'.hom = F.obj (𝟙_ C) ◁ ε.hom := by
    apply (cancel_epi (μ.app (𝟙_ C, 𝟙_ C)).hom).1
    apply (cancel_mono (ρ_ (F.obj (𝟙_ C))).hom).1
    simpa only [id_tensorHom, Category.assoc] using h
  let t : tensorLeft (F.obj (𝟙_ C)) ≅ 𝟭 D := NatIso.ofComponents
    (fun X ↦ whiskerRightIso e X ≪≫ λ_ X) (by
      intro X Y f
      change F.obj (𝟙_ C) ◁ f ≫ e.hom ▷ Y ≫ (λ_ Y).hom =
        (e.hom ▷ X ≫ (λ_ X).hom) ≫ f
      rw [whisker_exchange_assoc, leftUnitor_naturality]
      simp only [Category.assoc])
  have : (tensorLeft (F.obj (𝟙_ C))).Faithful := Functor.Faithful.of_iso t.symm
  exact (tensorLeft (F.obj (𝟙_ C))).map_injective hh

end CategoryTheory
