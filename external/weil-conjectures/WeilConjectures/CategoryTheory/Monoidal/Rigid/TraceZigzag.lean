/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# The trace through a coevaluation satisfying one zigzag identity

Let `C` be a symmetric monoidal category and `V` an object with a right dual. Let
`σ : 𝟙_ C ⟶ V ⊗ D` and `P : V ⊗ D ⟶ 𝟙_ C` satisfy the zigzag identity
```
V ≅ V ⊗ 𝟙 --V ◁ σ--> V ⊗ (V ⊗ D) ≅ (V ⊗ V) ⊗ D --β ▷ D--> (V ⊗ V) ⊗ D ≅ V ⊗ (V ⊗ D)
  --V ◁ P--> V ⊗ 𝟙 ≅ V
```
equal to the identity. Then for every endomorphism `v` of `V` the trace of `v` is
`P ∘ (v ⊗ D) ∘ σ` (`CategoryTheory.MonoidalCategory.trace_eq_of_zigzag`): the pair `(σ, P)`
computes traces like a duality datum, although `D` need not be a dual of `V`.

The argument transposes `P` into a map `t : D ⟶ Vᘁ`, shows `P = ε ∘ β ∘ (V ⊗ t)` and, from the
zigzag identity, `(V ⊗ t) ∘ σ = η`. Both steps use that the braiding is symmetric.
-/

@[expose] public section

namespace CategoryTheory.MonoidalCategory

open BraidedCategory

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
  (hsymm : ∀ X Y : C, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _)
  {V D : C} [HasRightDual V]

/-- The transpose `D ⟶ Vᘁ` of a pairing `P : V ⊗ D ⟶ 𝟙_ C`, through the symmetry. -/
noncomputable def pairingTranspose (P : V ⊗ D ⟶ 𝟙_ C) : D ⟶ Vᘁ :=
  (ρ_ D).inv ≫ D ◁ η_ V Vᘁ ≫ (α_ D V Vᘁ).inv ≫ ((β_ D V).hom ≫ P) ▷ Vᘁ ≫ (λ_ Vᘁ).hom

lemma pairingTranspose_whiskerRight_comp_evaluation (P : V ⊗ D ⟶ 𝟙_ C) :
    pairingTranspose P ▷ V ≫ ε_ V Vᘁ = (β_ D V).hom ≫ P := by
  calc
    _ = 𝟙 _ ⊗≫ D ◁ η_ V Vᘁ ▷ V ⊗≫ (((β_ D V).hom ≫ P) ▷ (Vᘁ ⊗ V) ≫ 𝟙_ C ◁ ε_ V Vᘁ) ⊗≫
        𝟙 _ := by
      simp only [pairingTranspose]; monoidal
    _ = 𝟙 _ ⊗≫ D ◁ (η_ V Vᘁ ▷ V ⊗≫ V ◁ ε_ V Vᘁ) ⊗≫ ((β_ D V).hom ≫ P) ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = _ := by
      rw [ExactPairing.evaluation_coevaluation'']; monoidal

include hsymm in
lemma whiskerLeft_pairingTranspose_comp (P : V ⊗ D ⟶ 𝟙_ C) :
    V ◁ pairingTranspose P ≫ (β_ V Vᘁ).hom ≫ ε_ V Vᘁ = P := by
  rw [BraidedCategory.braiding_naturality_right_assoc,
    pairingTranspose_whiskerRight_comp_evaluation, reassoc_of% (hsymm V D)]

include hsymm in
lemma comp_whiskerLeft_pairingTranspose (σ : 𝟙_ C ⟶ V ⊗ D) (P : V ⊗ D ⟶ 𝟙_ C)
    (hZ : (ρ_ V).inv ≫ V ◁ σ ≫ (α_ V V D).inv ≫ (β_ V V).hom ▷ D ≫ (α_ V V D).hom ≫ V ◁ P ≫
      (ρ_ V).hom = 𝟙 V) :
    σ ≫ V ◁ pairingTranspose P = η_ V Vᘁ := by
  have h₄ : (β_ (V ⊗ D) V).hom ≫ (α_ V V D).inv ≫ (β_ V V).hom ▷ D =
      (α_ V D V).hom ≫ V ◁ (β_ D V).hom ≫ (α_ V V D).inv := by
    rw [← cancel_epi (α_ V D V).inv, reassoc_of% (BraidedCategory.hexagon_reverse V D V)]
    simp only [← comp_whiskerRight, hsymm, MonoidalCategory.id_whiskerRight, Category.comp_id,
      Iso.inv_hom_id_assoc]
  have hσ : V ◁ σ ≫ (α_ V V D).inv ≫ (β_ V V).hom ▷ D =
      (ρ_ V).hom ≫ (λ_ V).inv ≫ σ ▷ V ≫ (α_ V D V).hom ≫ V ◁ (β_ D V).hom ≫
        (α_ V V D).inv := by
    have h₁ := BraidedCategory.braiding_naturality_left σ V
    rw [braiding_tensorUnit_left] at h₁
    have h₃ : V ◁ σ = (ρ_ V).hom ≫ (λ_ V).inv ≫ σ ▷ V ≫ (β_ (V ⊗ D) V).hom := by
      rw [h₁]; simp
    rw [h₃]
    simp only [Category.assoc, h₄]
  calc
    _ = 𝟙 _ ⊗≫ (σ ▷ 𝟙_ C ≫ (V ⊗ D) ◁ η_ V Vᘁ) ⊗≫ V ◁ (β_ D V).hom ▷ Vᘁ ⊗≫ V ◁ P ▷ Vᘁ ⊗≫
        𝟙 _ := by
      simp only [pairingTranspose]; monoidal
    _ = 𝟙 _ ⊗≫ η_ V Vᘁ ⊗≫ σ ▷ V ▷ Vᘁ ⊗≫ V ◁ (β_ D V).hom ▷ Vᘁ ⊗≫ V ◁ P ▷ Vᘁ ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]; monoidal
    _ = η_ V Vᘁ ≫ ((ρ_ V).inv ≫ (V ◁ σ ≫ (α_ V V D).inv ≫ (β_ V V).hom ▷ D) ≫
        (α_ V V D).hom ≫ V ◁ P ≫ (ρ_ V).hom) ▷ Vᘁ := by
      rw [hσ]; monoidal
    _ = η_ V Vᘁ ≫ ((ρ_ V).inv ≫ V ◁ σ ≫ (α_ V V D).inv ≫ (β_ V V).hom ▷ D ≫ (α_ V V D).hom ≫
        V ◁ P ≫ (ρ_ V).hom) ▷ Vᘁ := by
      simp only [Category.assoc]
    _ = _ := by rw [hZ, MonoidalCategory.id_whiskerRight, Category.comp_id]

include hsymm in
/-- **The trace through a coevaluation satisfying one zigzag identity.** In a symmetric monoidal
category, if `σ : 𝟙_ C ⟶ V ⊗ D` and `P : V ⊗ D ⟶ 𝟙_ C` satisfy the zigzag identity `hZ`, then
`tr(v) = P ∘ (v ⊗ D) ∘ σ` for every endomorphism `v` of the dualizable object `V`. -/
theorem trace_eq_of_zigzag (σ : 𝟙_ C ⟶ V ⊗ D) (P : V ⊗ D ⟶ 𝟙_ C)
    (hZ : (ρ_ V).inv ≫ V ◁ σ ≫ (α_ V V D).inv ≫ (β_ V V).hom ▷ D ≫ (α_ V V D).hom ≫ V ◁ P ≫
      (ρ_ V).hom = 𝟙 V) (v : V ⟶ V) :
    σ ≫ v ▷ D ≫ P = trace v := by
  calc
    σ ≫ v ▷ D ≫ P = σ ≫ v ▷ D ≫ V ◁ pairingTranspose P ≫ (β_ V Vᘁ).hom ≫ ε_ V Vᘁ := by
      rw [whiskerLeft_pairingTranspose_comp hsymm P]
    _ = (σ ≫ V ◁ pairingTranspose P) ≫ v ▷ Vᘁ ≫ (β_ V Vᘁ).hom ≫ ε_ V Vᘁ := by
      rw [← whisker_exchange_assoc, Category.assoc]
    _ = trace v := by rw [comp_whiskerLeft_pairingTranspose hsymm σ P hZ, trace]

end CategoryTheory.MonoidalCategory
