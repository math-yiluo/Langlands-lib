/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Transporting a zigzag identity along a monoidal functor

Let `F : P ⥤ S` be a monoidal functor between braided monoidal categories. On `P` let
`A : R ⟶ B ⊗ C` and a pairing `M ⊗ (B ⊗ C) ⟶ N` be given, of the shape of the transpose of the
Künneth–Verdier map: a braiding moving `M` next to `C`, a map `M ⊗ C ⟶ W` and a map
`exK : B ⊗ W ⟶ N`. Identifying `F M`, `F B` with `K`, `F C` with `D` and `F W` with `ω`, the
morphism `σ = (eB ⊗ eC) ∘ δ ∘ F A ∘ τ : 𝟙 ⟶ K ⊗ D` and the pairing `P = φ ∘ ev` satisfy the zigzag
identity of a duality as soon as `(M ◁ A) ≫ pairing` agrees with a morphism `Cl'` whose image
under `F` is the identity (`CategoryTheory.MonoidalCategory.zigzag_of_transport`). This is the
formal part of the point normalization of the trace class.
-/

@[expose] public section

namespace CategoryTheory.MonoidalCategory

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {S P : Type*} [Category S] [Category P] [MonoidalCategory S] [MonoidalCategory P]
  [BraidedCategory S] [BraidedCategory P] (F : P ⥤ S) [F.Monoidal]

/-- A rearrangement of whiskerings and braidings used in `zigzag_of_transport`. -/
lemma zigzag_rearrange {K D Z X₁ X₂ X₃ : S} (y : 𝟙_ S ⟶ X₂ ⊗ X₃) (eM : X₁ ≅ K) (eB : X₂ ⟶ K)
    (eC : X₃ ⟶ D) (g : K ⊗ D ⟶ Z) :
    K ◁ (y ≫ (eB ⊗ₘ eC)) ≫ (α_ K K D).inv ≫ (β_ K K).hom ▷ D ≫ (α_ K K D).hom ≫ K ◁ g =
      K ◁ y ≫ eM.inv ▷ (X₂ ⊗ X₃) ≫ (α_ _ _ _).inv ≫ (β_ X₁ X₂).hom ▷ X₃ ≫ (α_ _ _ _).hom ≫
        (eB ⊗ₘ ((eM.hom ⊗ₘ eC) ≫ g)) := by
  have h₁ : eM.inv ▷ X₃ ≫ (eM.hom ⊗ₘ eC) = K ◁ eC := by
    rw [tensorHom_def, ← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight,
      Category.id_comp]
  -- both sides are `K ◁ y ≫ α⁻¹ ≫ β ▷ X₃ ≫ α ≫ eB ▷ _ ≫ K ◁ (K ◁ eC ≫ g)`
  have hR : eM.inv ▷ (X₂ ⊗ X₃) ≫ (α_ _ _ _).inv ≫ (β_ X₁ X₂).hom ▷ X₃ ≫ (α_ _ _ _).hom ≫
      (eB ⊗ₘ ((eM.hom ⊗ₘ eC) ≫ g)) =
      (α_ _ _ _).inv ≫ (β_ K X₂).hom ▷ X₃ ≫ (α_ _ _ _).hom ≫ (eB ⊗ₘ (K ◁ eC ≫ g)) := by
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc,
      BraidedCategory.braiding_naturality_left, comp_whiskerRight_assoc,
      associator_naturality_middle_assoc, whiskerLeft_comp_tensorHom, ← reassoc_of% h₁]
  have hL : K ◁ (eB ⊗ₘ eC) ≫ (α_ K K D).inv ≫ (β_ K K).hom ▷ D ≫ (α_ K K D).hom ≫ K ◁ g =
      (α_ _ _ _).inv ≫ (β_ K X₂).hom ▷ X₃ ≫ (α_ _ _ _).hom ≫ (eB ⊗ₘ (K ◁ eC ≫ g)) := by
    rw [tensorHom_def, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      associator_inv_naturality_right_assoc, associator_inv_naturality_middle_assoc,
      whisker_exchange_assoc, ← comp_whiskerRight_assoc,
      BraidedCategory.braiding_naturality_right, comp_whiskerRight_assoc,
      associator_naturality_right_assoc, associator_naturality_left_assoc, tensorHom_def,
      MonoidalCategory.whiskerLeft_comp]
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, hL, hR]

/-- **Transport of a zigzag identity along a monoidal functor.** See the module docstring. -/
theorem zigzag_of_transport {K D ω : S} {M B C W N R T₁ : P} (A : R ⟶ B ⊗ C)
    (μ₂ : M ⊗ C ⟶ T₁) (ev₂ : T₁ ⟶ W) (exK : B ⊗ W ⟶ N) (Cl' : M ⊗ R ⟶ N)
    (hstar : M ◁ A ≫ (α_ M B C).inv ≫ (β_ M B).hom ▷ C ≫ (α_ B M C).hom ≫ B ◁ μ₂ ≫ B ◁ ev₂ ≫
      exK = Cl')
    (eM : F.obj M ≅ K) (eB : F.obj B ⟶ K) (eC : F.obj C ⟶ D) (eW : F.obj W ⟶ ω)
    (ev : K ⊗ D ⟶ ω) (φ : ω ⟶ 𝟙_ S) (χ : F.obj N ⟶ K) (τ : 𝟙_ S ⟶ F.obj R)
    (τ' : F.obj R ⟶ 𝟙_ S) (hτ : τ ≫ τ' = 𝟙 _)
    (hbraid : μ F M B ≫ F.map (β_ M B).hom = (β_ (F.obj M) (F.obj B)).hom ≫ μ F B M)
    (hμ₂ : μ F M C ≫ F.map μ₂ ≫ F.map ev₂ ≫ eW = (eM.hom ⊗ₘ eC) ≫ ev)
    (hK : μ F B W ≫ F.map exK ≫ χ = (eB ⊗ₘ eW) ≫ K ◁ φ ≫ (ρ_ K).hom)
    (hC : μ F M R ≫ F.map Cl' ≫ χ = F.obj M ◁ τ' ≫ (ρ_ _).hom ≫ eM.hom) :
    (ρ_ K).inv ≫ K ◁ (τ ≫ F.map A ≫ δ F B C ≫ (eB ⊗ₘ eC)) ≫ (α_ K K D).inv ≫
      (β_ K K).hom ▷ D ≫ (α_ K K D).hom ≫ K ◁ (ev ≫ φ) ≫ (ρ_ K).hom = 𝟙 K := by
  -- the transport `T(g) = ρ⁻¹ ≫ (eM⁻¹ ⊗ τ) ≫ μ ≫ F g ≫ χ` of `Cl'` is the identity
  have hT : (ρ_ K).inv ≫ (eM.inv ⊗ₘ τ) ≫ μ F M R ≫ F.map Cl' ≫ χ = 𝟙 K := by
    rw [hC, tensorHom_def']
    simp only [Category.assoc]
    rw [whisker_exchange_assoc, ← whiskerLeft_comp_assoc, hτ]
    simp
  rw [← hT, ← hstar]
  -- the image of the pairing under `F`
  have hP : μ F M (B ⊗ C) ≫ F.map ((α_ M B C).inv ≫ (β_ M B).hom ▷ C ≫ (α_ B M C).hom ≫
      B ◁ μ₂ ≫ B ◁ ev₂ ≫ exK) ≫ χ =
      F.obj M ◁ δ F B C ≫ (α_ _ _ _).inv ≫ (β_ (F.obj M) (F.obj B)).hom ▷ F.obj C ≫
        (α_ _ _ _).hom ≫ (eB ⊗ₘ ((eM.hom ⊗ₘ eC) ≫ ev)) ≫ K ◁ φ ≫ (ρ_ K).hom := by
    have h₁ : μ F M (B ⊗ C) = F.obj M ◁ δ F B C ≫ F.obj M ◁ μ F B C ≫ μ F M (B ⊗ C) := by
      rw [← whiskerLeft_comp_assoc, Functor.Monoidal.δ_μ, MonoidalCategory.whiskerLeft_id,
        Category.id_comp]
    have h₂ : F.obj B ◁ μ F M C ≫ F.obj B ◁ F.map μ₂ ≫ F.obj B ◁ F.map ev₂ ≫
        (eB ⊗ₘ eW) = (eB ⊗ₘ ((eM.hom ⊗ₘ eC) ≫ ev)) := by
      rw [← hμ₂, tensorHom_def', tensorHom_def']
      simp only [whiskerLeft_comp_assoc]
    rw [h₁, ← h₂]
    simp only [Category.assoc]
    rw [← hK]
    simp only [Functor.map_comp, Category.assoc]
    rw [Functor.LaxMonoidal.associativity_inv_assoc, ← μ_natural_left_assoc,
      ← comp_whiskerRight_assoc, hbraid,
      comp_whiskerRight_assoc, Functor.LaxMonoidal.associativity_assoc, ← μ_natural_right_assoc,
      ← μ_natural_right_assoc]
  rw [Functor.map_comp, tensorHom_def' eM.inv τ]
  simp only [Category.assoc]
  rw [← μ_natural_right_assoc, hP, ← whisker_exchange_assoc]
  have key := zigzag_rearrange (τ ≫ F.map A ≫ δ F B C) eM eB eC ev
  simp only [Category.assoc] at key
  rw [MonoidalCategory.whiskerLeft_comp K ev φ, Category.assoc, reassoc_of% key,
    ← whisker_exchange_assoc]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]

end CategoryTheory.MonoidalCategory
