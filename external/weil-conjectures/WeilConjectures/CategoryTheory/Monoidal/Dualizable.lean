/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Retract
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Stability properties of dualizable objects

In a monoidal category `C`:

- a zero object is dualizable when `C` is preadditive (`CategoryTheory.IsZero.isDualizable`),
  and the biproduct of a dualizable object with a zero object is dualizable
  (`CategoryTheory.IsDualizable.biprod_of_isZero_right`,
  `CategoryTheory.IsDualizable.biprod_of_isZero_left`);
- a retract of a dualizable object is dualizable when idempotents split
  (`CategoryTheory.IsDualizable.of_retract`);
- a binary biproduct of dualizable objects is dualizable when the tensor product is additive
  (`CategoryTheory.IsDualizable.biprod`).
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory

section Zero

variable {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C]

/-- A zero object of a preadditive monoidal category is dualizable, with itself as dual and
zero evaluation and coevaluation: both zig-zag identities are endomorphisms of an object
isomorphic to the zero object. -/
theorem IsZero.isDualizable {Z : C} (hZ : IsZero Z) : IsDualizable Z :=
  ⟨{ rightDual := Z
     exact :=
      { coevaluation' := 0
        evaluation' := 0
        coevaluation_evaluation' := (hZ.of_iso (ρ_ Z)).eq_of_src _ _
        evaluation_coevaluation' := (hZ.of_iso (λ_ Z)).eq_of_src _ _ } }⟩

/-- The biproduct of a dualizable object with a zero object is dualizable. -/
theorem IsDualizable.biprod_of_isZero_right [HasBinaryBiproducts C] {P Z : C}
    (hP : IsDualizable P) (hZ : IsZero Z) : IsDualizable (P ⊞ Z) :=
  hP.of_iso
    { hom := biprod.inl
      inv := biprod.fst
      hom_inv_id := by simp
      inv_hom_id := by
        rw [← biprod.total, hZ.eq_of_tgt biprod.snd 0, zero_comp, add_zero] }

/-- The biproduct of a zero object with a dualizable object is dualizable. -/
theorem IsDualizable.biprod_of_isZero_left [HasBinaryBiproducts C] {P Z : C}
    (hP : IsDualizable P) (hZ : IsZero Z) : IsDualizable (Z ⊞ P) :=
  hP.of_iso
    { hom := biprod.inr
      inv := biprod.snd
      hom_inv_id := by simp
      inv_hom_id := by
        rw [← biprod.total, hZ.eq_of_tgt biprod.fst 0, zero_comp, zero_add] }

end Zero

section Retract

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- A retract of an object with a right dual has a right dual when idempotents split: the dual is
the image of the idempotent `(r ≫ i)ᘁ` on the dual. -/
theorem nonempty_hasRightDual_of_retract [IsIdempotentComplete C] {R D : C} (h : Retract R D)
    [HasRightDual D] : Nonempty (HasRightDual R) := by
  have he : ((h.r ≫ h.i)ᘁ) ≫ ((h.r ≫ h.i)ᘁ) = (h.r ≫ h.i)ᘁ := by
    rw [← comp_rightAdjointMate, Category.assoc, h.retract_assoc]
  obtain ⟨S, s, p, hsp, hps⟩ := IsIdempotentComplete.idempotents_split _ _ he
  have k1 : ((p ≫ s) ⊗ₘ h.i) ≫ ε_ D Dᘁ = (Dᘁ ◁ h.i) ≫ ε_ D Dᘁ := by
    rw [hps, tensorHom_def', Category.assoc, rightAdjointMate_comp_evaluation,
      ← whiskerLeft_comp_assoc, h.retract_assoc]
  have k2 : η_ D Dᘁ ≫ ((h.r ≫ h.i) ⊗ₘ p) = η_ D Dᘁ ≫ (D ◁ p) := by
    rw [tensorHom_def, ← Category.assoc, ← coevaluation_comp_rightAdjointMate, Category.assoc,
      ← whiskerLeft_comp, ← hps, Category.assoc, hsp, Category.comp_id]
  exact ⟨
    { rightDual := S
      exact :=
        { coevaluation' := η_ D Dᘁ ≫ (h.r ⊗ₘ p)
          evaluation' := (s ⊗ₘ h.i) ≫ ε_ D Dᘁ
          coevaluation_evaluation' := by
            calc S ◁ (η_ D Dᘁ ≫ (h.r ⊗ₘ p)) ≫ (α_ S R S).inv ≫ ((s ⊗ₘ h.i) ≫ ε_ D Dᘁ) ▷ S
                = S ◁ η_ D Dᘁ ≫ (α_ S D Dᘁ).inv ≫ ((s ⊗ₘ (h.r ≫ h.i)) ⊗ₘ p) ≫
                  ε_ D Dᘁ ▷ S := by
                  rw [MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc]
                  congr 1
                  rw [← id_tensorHom, associator_inv_naturality_assoc, ← tensorHom_id,
                    ← tensorHom_id, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom]
                  simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
              _ = s ▷ _ ≫ Dᘁ ◁ (η_ D Dᘁ ≫ ((h.r ≫ h.i) ⊗ₘ p)) ≫ (α_ Dᘁ D S).inv ≫
                  ε_ D Dᘁ ▷ S := by
                  have e : (α_ S D Dᘁ).inv ≫ ((s ⊗ₘ (h.r ≫ h.i)) ⊗ₘ p) =
                      (s ⊗ₘ ((h.r ≫ h.i) ⊗ₘ p)) ≫ (α_ Dᘁ D S).inv :=
                    (associator_inv_naturality _ _ _).symm
                  rw [reassoc_of% e, tensorHom_def, Category.assoc, whisker_exchange_assoc]
                  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
              _ = s ▷ _ ≫ Dᘁ ◁ η_ D Dᘁ ≫ Dᘁ ◁ (D ◁ p) ≫ (α_ Dᘁ D S).inv ≫ ε_ D Dᘁ ▷ S := by
                  rw [k2, MonoidalCategory.whiskerLeft_comp, Category.assoc]
              _ = s ▷ _ ≫ Dᘁ ◁ η_ D Dᘁ ≫ (α_ Dᘁ D Dᘁ).inv ≫ ε_ D Dᘁ ▷ Dᘁ ≫ 𝟙_ C ◁ p := by
                  rw [associator_inv_naturality_right_assoc, whisker_exchange]
              _ = _ := by
                  rw [ExactPairing.coevaluation_evaluation_assoc, whiskerRight_id, id_whiskerLeft]
                  simp [reassoc_of% hsp]
          evaluation_coevaluation' := by
            calc (η_ D Dᘁ ≫ (h.r ⊗ₘ p)) ▷ R ≫ (α_ R S R).hom ≫ R ◁ ((s ⊗ₘ h.i) ≫ ε_ D Dᘁ)
                = η_ D Dᘁ ▷ R ≫ (α_ D Dᘁ R).hom ≫ (h.r ⊗ₘ (((p ≫ s) ⊗ₘ h.i) ≫ ε_ D Dᘁ)) := by
                  rw [comp_whiskerRight, Category.assoc, MonoidalCategory.whiskerLeft_comp]
                  congr 1
                  rw [← tensorHom_id, associator_naturality_assoc, ← id_tensorHom, ← id_tensorHom,
                    tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom]
                  simp only [Category.comp_id, Category.id_comp, tensorHom_comp_tensorHom]
              _ = η_ D Dᘁ ▷ R ≫ (α_ D Dᘁ R).hom ≫ D ◁ (Dᘁ ◁ h.i) ≫ D ◁ ε_ D Dᘁ ≫
                  h.r ▷ _ := by
                  rw [k1, tensorHom_def', MonoidalCategory.whiskerLeft_comp, Category.assoc]
              _ = 𝟙_ C ◁ h.i ≫ η_ D Dᘁ ▷ D ≫ (α_ D Dᘁ D).hom ≫ D ◁ ε_ D Dᘁ ≫ h.r ▷ _ := by
                  rw [← associator_naturality_right_assoc, whisker_exchange_assoc]
              _ = _ := by
                  rw [ExactPairing.evaluation_coevaluation_assoc, id_whiskerLeft, whiskerRight_id]
                  simp [h.retract_assoc] } }⟩

/-- A retract of a dualizable object is dualizable when idempotents split. -/
theorem IsDualizable.of_retract [IsIdempotentComplete C] {R D : C} (h : Retract R D)
    (hD : IsDualizable D) : IsDualizable R := by
  obtain ⟨_⟩ := hD
  exact nonempty_hasRightDual_of_retract h

end Retract

section Biprod

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- The composite of a coevaluation and an evaluation along maps through a common object only
depends on the composite of those maps. -/
lemma whiskerLeft_coevaluation_evaluation {A B M N N' : C} [HasRightDual A] [HasRightDual B]
    (i : A ⟶ M) (j : Aᘁ ⟶ N') (q : N ⟶ Bᘁ) (p : M ⟶ B) :
    N ◁ (η_ A Aᘁ ≫ (i ⊗ₘ j)) ≫ (α_ N M N').inv ≫ ((q ⊗ₘ p) ≫ ε_ B Bᘁ) ▷ N' =
      q ▷ 𝟙_ C ≫ Bᘁ ◁ η_ A Aᘁ ≫ (α_ Bᘁ A Aᘁ).inv ≫ (Bᘁ ◁ (i ≫ p)) ▷ Aᘁ ≫
        ε_ B Bᘁ ▷ Aᘁ ≫ 𝟙_ C ◁ j := by
  have e1 : N ◁ (i ⊗ₘ j) ≫ (α_ N M N').inv ≫ (q ⊗ₘ p) ▷ N' =
      (α_ N A Aᘁ).inv ≫ ((q ⊗ₘ (i ≫ p)) ⊗ₘ j) := by
    rw [← id_tensorHom, associator_inv_naturality_assoc, ← tensorHom_id,
      tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp]
  have e2 : (α_ N A Aᘁ).inv ≫ ((q ⊗ₘ (i ≫ p)) ⊗ₘ j) =
      (q ⊗ₘ (𝟙 A ⊗ₘ 𝟙 Aᘁ)) ≫ (α_ Bᘁ A Aᘁ).inv ≫ ((Bᘁ ◁ (i ≫ p)) ⊗ₘ j) := by
    rw [associator_inv_naturality_assoc, tensorHom_comp_tensorHom, ← id_tensorHom,
      tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp]
  rw [MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc, reassoc_of% e1,
    reassoc_of% e2, id_tensorHom_id]
  rw [tensorHom_id, whisker_exchange_assoc, tensorHom_def, Category.assoc, ← whisker_exchange]


/-- The composite of a coevaluation and an evaluation along maps through a common object only
depends on the composite of those maps. -/
lemma whiskerRight_coevaluation_evaluation {A B M N M' : C} [HasRightDual A] [HasRightDual B]
    (i : A ⟶ M) (j : Aᘁ ⟶ N) (q : N ⟶ Bᘁ) (p : M' ⟶ B) :
    (η_ A Aᘁ ≫ (i ⊗ₘ j)) ▷ M' ≫ (α_ M N M').hom ≫ M ◁ ((q ⊗ₘ p) ≫ ε_ B Bᘁ) =
      𝟙_ C ◁ p ≫ η_ A Aᘁ ▷ B ≫ (α_ A Aᘁ B).hom ≫ A ◁ ((j ≫ q) ▷ B) ≫
        A ◁ ε_ B Bᘁ ≫ i ▷ 𝟙_ C := by
  have e1 : (i ⊗ₘ j) ▷ M' ≫ (α_ M N M').hom ≫ M ◁ (q ⊗ₘ p) =
      (α_ A Aᘁ M').hom ≫ (i ⊗ₘ ((j ≫ q) ⊗ₘ p)) := by
    rw [← tensorHom_id, associator_naturality_assoc, ← id_tensorHom,
      tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp]
  have e2 : (α_ A Aᘁ M').hom ≫ (i ⊗ₘ ((j ≫ q) ⊗ₘ p)) =
      ((𝟙 A ⊗ₘ 𝟙 Aᘁ) ⊗ₘ p) ≫ (α_ A Aᘁ B).hom ≫ (i ⊗ₘ ((j ≫ q) ▷ B)) := by
    rw [associator_naturality_assoc, tensorHom_comp_tensorHom, ← tensorHom_id,
      tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp]
  rw [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc, reassoc_of% e1,
    reassoc_of% e2, id_tensorHom_id, id_tensorHom, ← whisker_exchange_assoc, tensorHom_def',
    Category.assoc, whisker_exchange]



variable [Preadditive C] [MonoidalPreadditive C] [HasBinaryBiproducts C]

/-- A binary biproduct of objects with right duals has a right dual, the biproduct of the duals. -/
theorem nonempty_hasRightDual_biprod {X Y : C} [HasRightDual X] [HasRightDual Y] :
    Nonempty (HasRightDual (X ⊞ Y)) :=
  ⟨{ rightDual := Xᘁ ⊞ Yᘁ
     exact :=
      { coevaluation' := η_ X Xᘁ ≫ (biprod.inl ⊗ₘ biprod.inl) +
          η_ Y Yᘁ ≫ (biprod.inr ⊗ₘ biprod.inr)
        evaluation' := (biprod.fst ⊗ₘ biprod.fst) ≫ ε_ X Xᘁ +
          (biprod.snd ⊗ₘ biprod.snd) ≫ ε_ Y Yᘁ
        coevaluation_evaluation' := by
          simp only [MonoidalPreadditive.whiskerLeft_add, MonoidalPreadditive.add_whiskerRight,
            Preadditive.add_comp, Preadditive.comp_add, whiskerLeft_coevaluation_evaluation,
            biprod.inl_fst,
            biprod.inl_snd, biprod.inr_fst, biprod.inr_snd, MonoidalCategory.whiskerLeft_id,
            id_whiskerRight, MonoidalPreadditive.whiskerLeft_zero,
            MonoidalPreadditive.zero_whiskerRight, zero_comp, comp_zero, add_zero, zero_add,
            Category.id_comp, ExactPairing.coevaluation_evaluation_assoc, whiskerRight_id,
            id_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc]
          rw [← Preadditive.comp_add, ← Category.assoc biprod.fst, ← Category.assoc biprod.snd,
            ← Preadditive.add_comp, biprod.total, Category.id_comp]
        evaluation_coevaluation' := by
          simp only [MonoidalPreadditive.whiskerLeft_add, MonoidalPreadditive.add_whiskerRight,
            Preadditive.add_comp, Preadditive.comp_add, whiskerRight_coevaluation_evaluation,
            biprod.inl_fst,
            biprod.inl_snd, biprod.inr_fst, biprod.inr_snd, MonoidalCategory.whiskerLeft_id,
            id_whiskerRight, MonoidalPreadditive.whiskerLeft_zero,
            MonoidalPreadditive.zero_whiskerRight, zero_comp, comp_zero, add_zero, zero_add,
            Category.id_comp, ExactPairing.evaluation_coevaluation_assoc, whiskerRight_id,
            id_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc]
          rw [← Preadditive.comp_add, ← Category.assoc biprod.fst, ← Category.assoc biprod.snd,
            ← Preadditive.add_comp, biprod.total, Category.id_comp] } }⟩

/-- A binary biproduct of dualizable objects is dualizable. -/
theorem IsDualizable.biprod {X Y : C} (hX : IsDualizable X) (hY : IsDualizable Y) :
    IsDualizable (X ⊞ Y) := by
  obtain ⟨_⟩ := hX
  obtain ⟨_⟩ := hY
  exact nonempty_hasRightDual_biprod

end Biprod

end CategoryTheory
