/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftUnitor

/-!
# The left unitor of the derived tensor product commutes with shifts

For every object `K` of `D(C)` and `n : ℤ`, the commutation of `𝟙_ ⊗ᴸ -` with the shift by `n`,
followed by the shifted left unitor, is the left unitor of `K⟦n⟧`. For `K = 𝟙_` this is
`DerivedCategory.leftUnitor_commShift`; the same argument applies to every object in the image
of the localization functor `CochainComplex C ℤ ⥤ D(C)`, through the compatibility of the left
unitor of cochain complexes with the shifts
(`CochainComplex.mapBifunctorShift₂Iso_hom_leftUnitor_hom`), and every object is isomorphic to
one of these.

## Main statements

- `DerivedCategory.leftUnitor_commShift_app`
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory

universe w v u

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

local instance hasColimitsOfSize_leftUnitorShift : HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink C

variable [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

open TensorCommShift₂ in
private lemma leftUnitor_liftingIsoApp_hom (K : CochainComplex C ℤ) :
    (Functor.CommShift₂OfLocalization.liftingIsoApp (LKFlat C) (L C)
      (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat (HomologicalComplex.quasiIso C (.up ℤ))
      (F C) (curriedTensor (DerivedCategory C)) (unitKFlat C)).app K ≫ (L C).map (λ_ K).hom =
        (λ_ ((L C).obj K)).hom := by
  have h := DerivedMonoidal.leftUnitor_hom_app Qh (HomotopyCategory.quasiIso C (.up ℤ))
    ((HomotopyCategory.quotient C _).obj K)
  have h' := HomotopyCategory.MonoidalCategory.leftUnitor_hom_app K
  exact (congrArg (_ ≫ Qh.map ·) h'.symm).trans h.symm

open TensorCommShift₂ in
/-- The left unitor of `D(C)` commutes with the shifts at the image of a cochain complex. -/
lemma leftUnitor_commShift_app_obj (K₀ : CochainComplex C ℤ) (n : ℤ) :
    (((curriedTensor (DerivedCategory C)).obj (𝟙_ _)).commShiftIso n).hom.app ((L C).obj K₀) ≫
      (λ_ ((L C).obj K₀)).hom⟦n⟧' = (λ_ (((L C).obj K₀)⟦n⟧)).hom := by
  have := Functor.CommShift₂OfLocalization.commShift_liftingIsoApp (M := ℤ) (LKFlat C) (L C)
    (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat (HomologicalComplex.quasiIso C (.up ℤ)) (F C)
    (curriedTensor (DerivedCategory C)) (unitKFlat C)
  have h₁ := NatTrans.shift_app_comm (Functor.CommShift₂OfLocalization.liftingIsoApp (LKFlat C)
    (L C) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat (HomologicalComplex.quasiIso C (.up ℤ))
    (F C) (curriedTensor (DerivedCategory C)) (unitKFlat C)) n K₀
  have hl := leftUnitor_liftingIsoApp_hom C
  rw [Functor.commShiftIso_comp_hom_app] at h₁
  have h₂ : (((F C).obj (unitKFlat C)).commShiftIso n).hom.app K₀ =
      (L C).map (CochainComplex.mapBifunctorShift₂Iso (𝟙_ _) K₀ (curriedTensor C) n).hom ≫
        ((L C).commShiftIso n).hom.app _ := by
    erw [Functor.commShiftIso_comp_hom_app]
    rfl
  rw [h₂] at h₁
  simp only [assoc] at h₁
  have hA := leftUnitor_naturality (((L C).commShiftIso n).hom.app K₀)
  have hE := ((L C).commShiftIso_hom_naturality (λ_ K₀).hom n).symm
  have hF := CochainComplex.mapBifunctorShift₂Iso_hom_leftUnitor_hom K₀ n
  rw [← cancel_epi (((curriedTensor (DerivedCategory C)).obj (𝟙_ _)).map
    (((L C).commShiftIso n).hom.app K₀))]
  erw [hA, ← hl (K₀⟦n⟧), ← hl K₀]
  rw [(shiftFunctor (DerivedCategory C) n).map_comp]
  erw [reassoc_of% h₁]
  rw [assoc]
  congr 1
  have hG : (L C).map (CochainComplex.mapBifunctorShift₂Iso (𝟙_ (CochainComplex C ℤ)) K₀
      (curriedTensor C) n).hom ≫ ((L C).commShiftIso n).hom.app _ ≫
        ((L C).map (λ_ K₀).hom)⟦n⟧' =
      (L C).map (λ_ (K₀⟦n⟧)).hom ≫ ((L C).commShiftIso n).hom.app _ := by
    erw [hE]
    rw [← Functor.map_comp_assoc, hF]
  exact hG

open TensorCommShift₂ in
/-- The left unitor of `D(C)` commutes with the shifts: the commutation of `𝟙_ ⊗ᴸ -` with the
shift by `n`, followed by the shifted unitor, is the unitor of the shifted object. -/
lemma leftUnitor_commShift_app (K : DerivedCategory C) (n : ℤ) :
    (((curriedTensor (DerivedCategory C)).obj (𝟙_ _)).commShiftIso n).hom.app K ≫
      (λ_ K).hom⟦n⟧' = (λ_ (K⟦n⟧)).hom := by
  obtain ⟨K₀, ⟨e⟩⟩ : ∃ K₀, Nonempty ((L C).obj K₀ ≅ K) :=
    ⟨_, ⟨(L C).objObjPreimageIso K⟩⟩
  have h := leftUnitor_commShift_app_obj C K₀ n
  rw [← cancel_epi (((curriedTensor (DerivedCategory C)).obj (𝟙_ _)).map (e.hom⟦n⟧'))]
  have h₁ := (((curriedTensor (DerivedCategory C)).obj (𝟙_ _)).commShiftIso n).hom.naturality e.hom
  simp only [Functor.comp_map] at h₁
  rw [reassoc_of% h₁, ← Functor.map_comp]
  erw [leftUnitor_naturality]
  rw [Functor.map_comp, reassoc_of% h]
  exact (leftUnitor_naturality _).symm

end DerivedCategory
