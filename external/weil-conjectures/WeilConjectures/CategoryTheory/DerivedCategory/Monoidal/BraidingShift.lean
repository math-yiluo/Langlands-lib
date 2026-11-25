/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.BraidingShift
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
public import WeilConjectures.CategoryTheory.Monoidal.BraidingShiftAux
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided

/-!
# The Koszul braiding of the derived tensor product commutes with the shifts

For `X Y` in the derived category `D(C)`, with the Koszul braiding
`DerivedCategory.braidedCategory'`, the square
```
X ⊗ᴸ Y⟦y⟧ ──── β ────▶ Y⟦y⟧ ⊗ᴸ X
    │                     │
    ▼                     ▼
(X ⊗ᴸ Y)⟦y⟧ ──β⟦y⟧──▶ (Y ⊗ᴸ X)⟦y⟧
```
commutes, the vertical maps being the commutations of `X ⊗ᴸ -` and `- ⊗ᴸ X` with the shifts
(`DerivedCategory.braiding_hom_commShiftIso_hom_app`). For `X` the image of a K-flat complex and
`Y` the image of a complex it is transported from the homotopy category
(`HomotopyCategory.braiding_hom_commShiftIso_hom_app`) through the comparison maps of the
localization, which commute with the shifts (`DerivedCategory.commShift_tensorLeftCounit`) and
with the braidings (`DerivedMonoidal.braiding_hom_μ`); the general case follows by naturality.
-/

@[expose] public section

universe w v

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

variable {C : Type*} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

local instance hasColimitsOfSize_braidingShift : HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink C

variable [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

attribute [local instance] DerivedCategory.braidedCategory'

/-- The braiding commutes with the shifts on images of homotopy classes, the first one K-flat. -/
lemma braiding_hom_commShiftIso_hom_app_Qh (P Z : HomotopyCategory C (.up ℤ))
    (hP : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat P) (y : ℤ) :
    (β_ (Qh.obj P) ((Qh.obj Z)⟦y⟧)).hom ≫
        (((curriedTensor (DerivedCategory C)).flip.obj (Qh.obj P)).commShiftIso y).hom.app
          (Qh.obj Z) =
      (((curriedTensor (DerivedCategory C)).obj (Qh.obj P)).commShiftIso y).hom.app (Qh.obj Z) ≫
        ((β_ (Qh.obj P) (Qh.obj Z)).hom)⟦y⟧' := by
  have := commShift_tensorLeftCounit P hP
  have := commShift_tensorRightCounit P hP
  have := isIso_tensorRightCounit P hP
  have hL := NatTrans.shift_app_comm (tensorLeftCounit P) y Z
  have hR := NatTrans.shift_app_comm (tensorRightCounit P) y Z
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hL hR
  have hβ₁ : (β_ (Qh.obj P) (Qh.obj (Z⟦y⟧))).hom ≫ (tensorRightCounit P).app (Z⟦y⟧) =
      (tensorLeftCounit P).app (Z⟦y⟧) ≫ Qh.map (β_ P (Z⟦y⟧)).hom :=
    DerivedMonoidal.braiding_hom_μ Qh (HomotopyCategory.quasiIso C (.up ℤ)) P (Z⟦y⟧)
  have hβ₂ : (β_ (Qh.obj P) (Qh.obj Z)).hom ≫ (tensorRightCounit P).app Z =
      (tensorLeftCounit P).app Z ≫ Qh.map (β_ P Z).hom :=
    DerivedMonoidal.braiding_hom_μ Qh (HomotopyCategory.quasiIso C (.up ℤ)) P Z
  have hH := Qh.congr_map (HomotopyCategory.braiding_hom_commShiftIso_hom_app P Z y)
  simp only [Functor.map_comp] at hH
  have hQ := Qh.commShiftIso_hom_naturality (β_ P Z).hom y
  exact braiding_hom_comp_aux (shiftFunctor (DerivedCategory C) y) _ _ _ _ _ _ _ _ _ _ _ _ _
    _ hL hR hβ₁ hβ₂ hH hQ

/-- **The Koszul braiding of the derived tensor product commutes with the shifts.** -/
@[reassoc]
lemma braiding_hom_commShiftIso_hom_app (X Y : DerivedCategory C) (y : ℤ) :
    (β_ X (Y⟦y⟧)).hom ≫
        (((curriedTensor (DerivedCategory C)).flip.obj X).commShiftIso y).hom.app Y =
      (((curriedTensor (DerivedCategory C)).obj X).commShiftIso y).hom.app Y ≫
        ((β_ X Y).hom)⟦y⟧' := by
  obtain ⟨P, hP, ⟨eX⟩⟩ := exists_kFlat_iso X
  refine braiding_hom_comp_of_iso_left (shiftFunctor (DerivedCategory C) y) eX.symm _ _ _ _
    (NatTrans.shift_app_comm ((curriedTensor (DerivedCategory C)).map eX.symm.hom) y Y).symm
    (NatTrans.shift_app_comm ((curriedTensor (DerivedCategory C)).flip.map eX.symm.hom) y Y).symm
    ?_
  refine braiding_hom_comp_of_iso_right (shiftFunctor (DerivedCategory C) y)
    (Qh.objObjPreimageIso Y).symm _ _ _ _
    (((curriedTensor (DerivedCategory C)).obj (Qh.obj P)).commShiftIso_hom_naturality
      (Qh.objObjPreimageIso Y).symm.hom y)
    (((curriedTensor (DerivedCategory C)).flip.obj (Qh.obj P)).commShiftIso_hom_naturality
      (Qh.objObjPreimageIso Y).symm.hom y) ?_
  exact braiding_hom_commShiftIso_hom_app_Qh P (Qh.objPreimage Y) hP y

end DerivedCategory
