/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.Monoidal.ShiftProduct
public import WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift

/-!
# The unitors of the derived tensor product commute with the shifts

The unit `𝟙_` of the derived category `D(C)` is the image of the unit complex, which is K-flat.
Through the localization functor, the unitors of `D(C)` are those of cochain complexes, and the
commutation isomorphisms of `𝟙_ ⊗ᴸ -` and `- ⊗ᴸ 𝟙_` with the shifts are those of `𝟙_ ⊗ -` and
`- ⊗ 𝟙_`, which are compatible with the unitors
(`CochainComplex.mapBifunctorShift₂Iso_hom_leftUnitor_hom`,
`CochainComplex.mapBifunctorShift₁Iso_hom_rightUnitor_hom`). Hence the unitors of `D(C)`
commute with the shifts (`DerivedCategory.unitorsCommShift`), so that the product of
classes of the unit of `D(C)` is graded commutative.

## Main statements

- `DerivedCategory.unitorsCommShift`: the unitors of `𝟙_` commute with the shifts.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory

universe w v u

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

local instance hasColimitsOfSize_shiftUnitor : HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink C

variable [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

namespace TensorCommShift₂

/-- The unit complex, as a K-flat complex. -/
noncomputable def unitKFlat : CochainComplex.KFlat C :=
  ⟨𝟙_ _, (CochainComplex.kFlat_single_obj_iff_flat _ 0).2
    (ObjectProperty.prop_unit ObjectProperty.flat)⟩

end TensorCommShift₂

open TensorCommShift₂ in
lemma leftUnitor_commShift (n : ℤ) :
    (((curriedTensor (DerivedCategory C)).obj (𝟙_ _)).commShiftIso n).hom.app (𝟙_ _) ≫
      (λ_ (𝟙_ (DerivedCategory C))).hom⟦n⟧' = (λ_ ((𝟙_ (DerivedCategory C))⟦n⟧)).hom := by
  -- Reuse the coproduct and graded tensor instances throughout the comparison.
  have (J : Type) : HasColimitsOfShape (Discrete J) C := inferInstance
  have (X₁ X₂ : GradedObject ℤ C) : X₁.HasTensor X₂ := inferInstance
  have (X₁ X₂ X₃ X₄ : GradedObject ℤ C) :
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
  have (X₁ X₂ X₃ : GradedObject ℤ C) :
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
  have (X₁ X₂ X₃ : GradedObject ℤ C) :
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
  have := Functor.CommShift₂OfLocalization.commShift_liftingIsoApp (M := ℤ) (LKFlat C) (L C)
    (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat (HomologicalComplex.quasiIso C (.up ℤ)) (F C)
    (curriedTensor (DerivedCategory C)) (unitKFlat C)
  have h₁ := NatTrans.shift_app_comm (Functor.CommShift₂OfLocalization.liftingIsoApp (LKFlat C)
    (L C) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat (HomologicalComplex.quasiIso C (.up ℤ))
    (F C) (curriedTensor (DerivedCategory C)) (unitKFlat C)) n (𝟙_ _)
  have hl (K : CochainComplex C ℤ) : (Functor.CommShift₂OfLocalization.liftingIsoApp (LKFlat C)
      (L C) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat (HomologicalComplex.quasiIso C (.up ℤ))
      (F C) (curriedTensor (DerivedCategory C)) (unitKFlat C)).app K ≫ (L C).map (λ_ K).hom =
        (λ_ ((L C).obj K)).hom := by
    have h := DerivedMonoidal.leftUnitor_hom_app Qh (HomotopyCategory.quasiIso C (.up ℤ))
      ((HomotopyCategory.quotient C _).obj K)
    have h' := HomotopyCategory.MonoidalCategory.leftUnitor_hom_app K
    exact (congrArg (_ ≫ Qh.map ·) h'.symm).trans h.symm
  rw [Functor.commShiftIso_comp_hom_app] at h₁
  have h₂ : (((F C).obj (unitKFlat C)).commShiftIso n).hom.app (𝟙_ _) =
      (L C).map (CochainComplex.mapBifunctorShift₂Iso (𝟙_ _) (𝟙_ _) (curriedTensor C) n).hom ≫
        ((L C).commShiftIso n).hom.app _ := by
    erw [Functor.commShiftIso_comp_hom_app]
    rfl
  rw [h₂] at h₁
  simp only [assoc] at h₁
  have hA : ((curriedTensor (DerivedCategory C)).obj (𝟙_ _)).map
      (((L C).commShiftIso n).hom.app (𝟙_ _)) ≫ (λ_ ((𝟙_ (DerivedCategory C))⟦n⟧)).hom =
        (λ_ ((L C).obj ((𝟙_ (CochainComplex C ℤ))⟦n⟧))).hom ≫
          ((L C).commShiftIso n).hom.app (𝟙_ _) :=
    leftUnitor_naturality _
  have hC : (λ_ (𝟙_ (DerivedCategory C))).hom = (Functor.CommShift₂OfLocalization.liftingIsoApp
      (LKFlat C) (L C) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
      (HomologicalComplex.quasiIso C (.up ℤ)) (F C) (curriedTensor (DerivedCategory C))
      (unitKFlat C)).app (𝟙_ _) ≫ (L C).map (λ_ (𝟙_ (CochainComplex C ℤ))).hom :=
    (hl _).symm
  have hE := ((L C).commShiftIso_hom_naturality (λ_ (𝟙_ (CochainComplex C ℤ))).hom n).symm
  have hF := CochainComplex.mapBifunctorShift₂Iso_hom_leftUnitor_hom (𝟙_ (CochainComplex C ℤ)) n
  rw [← cancel_epi (((curriedTensor (DerivedCategory C)).obj (𝟙_ _)).map
    (((L C).commShiftIso n).hom.app (𝟙_ _))), hA, ← hl, hC, Functor.map_comp]
  erw [reassoc_of% h₁]
  rw [assoc]
  congr 1
  have hG : (L C).map (CochainComplex.mapBifunctorShift₂Iso (𝟙_ (CochainComplex C ℤ)) (𝟙_ _)
      (curriedTensor C) n).hom ≫ ((L C).commShiftIso n).hom.app _ ≫
        ((L C).map (λ_ (𝟙_ (CochainComplex C ℤ))).hom)⟦n⟧' =
      (L C).map (λ_ ((𝟙_ (CochainComplex C ℤ))⟦n⟧)).hom ≫ ((L C).commShiftIso n).hom.app _ := by
    erw [hE]
    rw [← Functor.map_comp_assoc, hF]
  exact hG

open TensorCommShift₂ in
lemma rightUnitor_commShift (n : ℤ) :
    (((curriedTensor (DerivedCategory C)).flip.obj (𝟙_ _)).commShiftIso n).hom.app (𝟙_ _) ≫
      (ρ_ (𝟙_ (DerivedCategory C))).hom⟦n⟧' = (ρ_ ((𝟙_ (DerivedCategory C))⟦n⟧)).hom := by
  -- Reuse the coproduct and graded tensor instances throughout the comparison.
  have (J : Type) : HasColimitsOfShape (Discrete J) C := inferInstance
  have (X₁ X₂ : GradedObject ℤ C) : X₁.HasTensor X₂ := inferInstance
  have (X₁ X₂ X₃ X₄ : GradedObject ℤ C) :
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
  have (X₁ X₂ X₃ : GradedObject ℤ C) :
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
  have (X₁ X₂ X₃ : GradedObject ℤ C) :
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
  have := Functor.CommShift₂OfLocalization.commShift_liftingIsoApp (M := ℤ) (L C) (LKFlat C)
    (HomologicalComplex.quasiIso C (.up ℤ)) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
    (F C).flip (curriedTensor (DerivedCategory C)).flip (𝟙_ _)
  have h₁ := NatTrans.shift_app_comm (Functor.CommShift₂OfLocalization.liftingIsoApp (L C)
    (LKFlat C) (HomologicalComplex.quasiIso C (.up ℤ))
    (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
    (F C).flip (curriedTensor (DerivedCategory C)).flip (𝟙_ _)) n (unitKFlat C)
  rw [Functor.commShiftIso_comp_hom_app] at h₁
  have hr (P : CochainComplex.KFlat C) : (Functor.CommShift₂OfLocalization.liftingIsoApp (L C)
      (LKFlat C) (HomologicalComplex.quasiIso C (.up ℤ))
      (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat (F C).flip
      (curriedTensor (DerivedCategory C)).flip (𝟙_ _)).app P ≫ (L C).map (ρ_ P.obj).hom =
        (ρ_ ((LKFlat C).obj P)).hom := by
    have h := DerivedMonoidal.rightUnitor_hom_app Qh (HomotopyCategory.quasiIso C (.up ℤ))
      ((HomotopyCategory.quotient C _).obj P.obj)
    have h' := HomotopyCategory.MonoidalCategory.rightUnitor_hom_app P.obj
    exact (congrArg (_ ≫ Qh.map ·) h'.symm).trans h.symm
  have h₂ : (((F C).flip.obj (𝟙_ _)).commShiftIso n).hom.app (unitKFlat C) =
      (L C).map (((CochainComplex.ιKFlat C).commShiftIso n).hom.app (unitKFlat C) ▷ 𝟙_ _ ≫
        (CochainComplex.mapBifunctorShift₁Iso (𝟙_ _) (𝟙_ _) (curriedTensor C) n).hom) ≫
        ((L C).commShiftIso n).hom.app _ := by
    erw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app]
    rfl
  have h₃ : ((LKFlat C).commShiftIso n).hom.app (unitKFlat C) =
      (L C).map (((CochainComplex.ιKFlat C).commShiftIso n).hom.app (unitKFlat C)) ≫
      ((L C).commShiftIso n).hom.app (𝟙_ _) :=
    Functor.commShiftIso_comp_hom_app _ _ _ _
  rw [h₂, h₃] at h₁
  simp only [assoc] at h₁
  have hA : ((curriedTensor (DerivedCategory C)).flip.obj (𝟙_ _)).map
      ((L C).map (((CochainComplex.ιKFlat C).commShiftIso n).hom.app (unitKFlat C)) ≫
        ((L C).commShiftIso n).hom.app (𝟙_ _)) ≫ (ρ_ ((𝟙_ (DerivedCategory C))⟦n⟧)).hom =
      (ρ_ ((LKFlat C).obj ((unitKFlat C)⟦n⟧))).hom ≫
        (L C).map (((CochainComplex.ιKFlat C).commShiftIso n).hom.app (unitKFlat C)) ≫
          ((L C).commShiftIso n).hom.app (𝟙_ _) :=
    rightUnitor_naturality _
  have hC : (ρ_ (𝟙_ (DerivedCategory C))).hom = (Functor.CommShift₂OfLocalization.liftingIsoApp
      (L C) (LKFlat C) (HomologicalComplex.quasiIso C (.up ℤ))
      (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat (F C).flip
      (curriedTensor (DerivedCategory C)).flip (𝟙_ _)).app (unitKFlat C) ≫
        (L C).map (ρ_ (𝟙_ (CochainComplex C ℤ))).hom :=
    (hr (unitKFlat C)).symm
  have hE := ((L C).commShiftIso_hom_naturality (ρ_ (𝟙_ (CochainComplex C ℤ))).hom n).symm
  have hF := CochainComplex.mapBifunctorShift₁Iso_hom_rightUnitor_hom (𝟙_ (CochainComplex C ℤ)) n
  have hN := rightUnitor_naturality
    (((CochainComplex.ιKFlat C).commShiftIso n).hom.app (unitKFlat C))
  rw [← cancel_epi (((curriedTensor (DerivedCategory C)).flip.obj (𝟙_ _)).map
      ((L C).map (((CochainComplex.ιKFlat C).commShiftIso n).hom.app (unitKFlat C)) ≫
        ((L C).commShiftIso n).hom.app (𝟙_ _))), hA]
  have hB := hr ((unitKFlat C)⟦n⟧)
  rw [← hB, hC, (shiftFunctor (DerivedCategory C) n).map_comp]
  erw [reassoc_of% h₁]
  rw [assoc]
  congr 1
  have hG : (L C).map (((CochainComplex.ιKFlat C).commShiftIso n).hom.app (unitKFlat C) ▷ 𝟙_ _ ≫
      (CochainComplex.mapBifunctorShift₁Iso (𝟙_ _) (𝟙_ _) (curriedTensor C) n).hom) ≫
        ((L C).commShiftIso n).hom.app _ ≫
          ((L C).map (ρ_ (𝟙_ (CochainComplex C ℤ))).hom)⟦n⟧' =
      (L C).map (ρ_ ((unitKFlat C)⟦n⟧).obj).hom ≫
        (L C).map (((CochainComplex.ιKFlat C).commShiftIso n).hom.app (unitKFlat C)) ≫
          ((L C).commShiftIso n).hom.app (𝟙_ _) := by
    erw [hE]
    rw [← Functor.map_comp_assoc, assoc, hF]
    erw [hN]
    rw [Functor.map_comp_assoc]
    rfl
  exact hG


/-- The unitors of `𝟙_` in the derived category commute with the shifts. -/
lemma unitorsCommShift : UnitorsCommShift (DerivedCategory C) where
  leftUnitor := leftUnitor_commShift C
  rightUnitor := rightUnitor_commShift C

end DerivedCategory
