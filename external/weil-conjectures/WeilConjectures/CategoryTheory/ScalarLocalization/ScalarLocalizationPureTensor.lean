/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationFullSubcategory
public import Mathlib.CategoryTheory.Retract

/-! # Pure tensors in a scalar localization

Composition of pure tensors `a ⊗ f` in the scalar localization `ScalarLocalization R C p`
(`CategoryTheory.ScalarLocalization.tmul_comp_tmul`), the retract obtained from an
integral splitting `s ≫ μ = p ^ n • 𝟙` by inverting `p`
(`CategoryTheory.ScalarLocalization.retractOfSmulSplit`), and the inclusion of a localized
full subcategory on pure tensors
(`CategoryTheory.ScalarLocalization.fullSubcategoryInclusion_map_tmul`), which is additive.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open TensorProduct

namespace CategoryTheory.ScalarLocalization

variable {R : Type*} [CommRing R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
  {p : R}

/-- Composition of pure tensors in a scalar localization. -/
theorem tmul_comp_tmul {K L M : ScalarLocalization R C p} (a b : Localization.Away p)
    (f : K.obj ⟶ L.obj) (g : L.obj ⟶ M.obj) :
    @Eq (K ⟶ M) ((a ⊗ₜ[R] f : K ⟶ L) ≫ (b ⊗ₜ[R] g : L ⟶ M)) ((b * a) ⊗ₜ[R] (f ≫ g)) :=
  composition_tmul R C p K.obj L.obj M.obj g f b a

/-- In a scalar localization, an integral split up to a power of the inverted element
gives a retract. -/
def retractOfSmulSplit {X Y : C} (n : ℕ) (s : X ⟶ Y) (μ : Y ⟶ X)
    (h : s ≫ μ = p ^ n • 𝟙 X) :
    Retract (ScalarLocalization.mk (R := R) (C := C) (p := p) X)
      (ScalarLocalization.mk (R := R) (C := C) (p := p) Y) where
  i := (1 : Localization.Away p) ⊗ₜ[R] s
  r := (IsLocalization.Away.invSelf (S := Localization.Away p) p ^ n) ⊗ₜ[R] μ
  retract := by
    refine (ScalarLocalization.composition_tmul R C p X Y X μ s _ _).trans ?_
    rw [h, mul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
      map_pow, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow]
    rfl

/-- The inclusion of a localized full subcategory on pure tensors. -/
theorem fullSubcategoryInclusion_map_tmul (P : ObjectProperty C)
    {K M : ScalarLocalization R P.FullSubcategory p} (a : Localization.Away p)
    (f : K.obj ⟶ M.obj) :
    (fullSubcategoryInclusion R C P p).map (a ⊗ₜ[R] f : K ⟶ M) = a ⊗ₜ[R] f.hom :=
  TensorProduct.congr_tmul _ _ a f

/-- The inclusion of a localized full subcategory is additive. -/
instance fullSubcategoryInclusion_additive (P : ObjectProperty C) :
    (fullSubcategoryInclusion R C P p).Additive :=
  ⟨fun {_ _ f g} ↦ map_add (TensorProduct.congr _ _) f g⟩

end CategoryTheory.ScalarLocalization
