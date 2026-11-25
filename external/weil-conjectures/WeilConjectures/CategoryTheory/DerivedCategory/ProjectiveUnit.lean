/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-!
# Derived categories with a projective unit

Let `C` be a monoidal abelian category whose derived category `D(C)` carries the derived tensor
product. If the unit `𝟙_ C` is projective, then the unit of `D(C)`, which is `𝟙_ C` placed in
degree `0`, has no nonzero morphisms to its positive shifts: `Ext^n(𝟙_, 𝟙_) = 0` for `n > 0`.

## Main results

- `DerivedCategory.unit_hom_shift_eq_zero_of_projective`: if `𝟙_ C` is projective, every
  morphism `𝟙_ ⟶ (𝟙_)⟦n⟧` in `D(C)` with `0 < n` is zero.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]

/-- If the unit of `C` is projective, every morphism `𝟙_ ⟶ (𝟙_)⟦n⟧` in `D(C)` with `0 < n` is
zero: the unit of `D(C)` is the projective object `𝟙_ C` placed in degree `0`. -/
lemma unit_hom_shift_eq_zero_of_projective [Projective (𝟙_ C)] (n : ℤ) (hn : 0 < n)
    (φ : 𝟙_ (DerivedCategory C) ⟶ (𝟙_ _)⟦n⟧) : φ = 0 := by
  let e₁ : 𝟙_ (DerivedCategory C) ≅ Q.obj ((CochainComplex.singleFunctor C 0).obj (𝟙_ C)) :=
    (singleFunctorObjUnitIso C).symm ≪≫ (singleFunctorIsoCompQ C 0).app _
  let e₂ : (𝟙_ (DerivedCategory C))⟦n⟧ ≅
      Q.obj ((CochainComplex.singleFunctor C (-n)).obj (𝟙_ C)) :=
    (shiftFunctor _ n).mapIso (singleFunctorObjUnitIso C).symm ≪≫
      ((singleFunctors C).shiftIso n (-n) 0 (by lia)).app _ ≪≫
      (singleFunctorIsoCompQ C (-n)).app _
  have h : e₁.inv ≫ φ ≫ e₂.hom = 0 :=
    from_singleFunctor_obj_eq_zero_of_projective _ (-n) (by lia)
  rw [← cancel_epi e₁.inv, ← cancel_mono e₂.hom, comp_zero, zero_comp, Category.assoc, h]

end DerivedCategory
