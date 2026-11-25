/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.SchemeCanonicalTensorShift
import WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift

/-! # The canonical tensor shift and the right unitor

Source: Stacks Project, Tag 06YH, total tensor localization and the Koszul unitor identity.
(blueprint: lem-sc-scheme-canonical-tensor-shift-right-unitor).
-/

@[expose] public section
set_option autoImplicit false
universe u w v s
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits MonoidalCategory
namespace DerivedCategory

variable (C : Type u) [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{s} C]
  [HasDerivedCategory.{v} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C] [HasColimitsOfSize.{0, 0} C]
  [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

attribute [local instance] commShift₂CurriedTensor

open DerivedCategory.TensorCommShift₂ in
private lemma rightUnitor_liftingIsoApp_hom (P : CochainComplex.KFlat C) :
    (Functor.CommShift₂OfLocalization.liftingIsoApp (L C) (LKFlat C)
      (HomologicalComplex.quasiIso C (.up ℤ)) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
      (F C).flip (curriedTensor (DerivedCategory C)).flip (𝟙_ _)).app P ≫
        (L C).map (ρ_ P.obj).hom =
      (ρ_ ((LKFlat C).obj P)).hom := by
  have h := DerivedMonoidal.rightUnitor_hom_app Qh (HomotopyCategory.quasiIso C (.up ℤ))
    ((HomotopyCategory.quotient C _).obj P.obj)
  have h' := HomotopyCategory.MonoidalCategory.rightUnitor_hom_app P.obj
  exact (congrArg (_ ≫ Qh.map ·) h'.symm).trans h.symm

open DerivedCategory.TensorCommShift₂ in
omit [Abelian.HasFunctorialFlatResolution C] [HasColimitsOfSize.{0, 0} C]
  [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (.up ℤ))] in
private lemma rightUnitor_shift_tensor_hom (P : CochainComplex.KFlat C) (n : ℤ) :
    (((F C).flip.obj (𝟙_ _)).commShiftIso n).hom.app P =
      (L C).map (((CochainComplex.ιKFlat C).commShiftIso n).hom.app P ▷ 𝟙_ _ ≫
        (CochainComplex.mapBifunctorShift₁Iso P.obj (𝟙_ _) (curriedTensor C) n).hom) ≫
        ((L C).commShiftIso n).hom.app _ := by
  erw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app]
  rfl

open DerivedCategory.TensorCommShift₂ in
private lemma rightUnitor_shift_lifting_square (P : CochainComplex.KFlat C) (n : ℤ) :
    let a := ((CochainComplex.ιKFlat C).commShiftIso n).hom.app P
    let η := Functor.CommShift₂OfLocalization.liftingIsoApp (L C) (LKFlat C)
      (HomologicalComplex.quasiIso C (.up ℤ)) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
      (F C).flip (curriedTensor (DerivedCategory C)).flip (𝟙_ _)
    ((curriedTensor (DerivedCategory C)).flip.obj
        ((L C).obj (𝟙_ (CochainComplex C ℤ)))).map
        ((L C).map a ≫ ((L C).commShiftIso n).hom.app P.obj) ≫
      (((curriedTensor (DerivedCategory C)).flip.obj
        ((L C).obj (𝟙_ (CochainComplex C ℤ)))).commShiftIso n).hom.app
        ((LKFlat C).obj P) ≫ (η.app P)⟦n⟧' =
      η.app (P⟦n⟧) ≫
        (L C).map (a ▷ 𝟙_ _ ≫
          (CochainComplex.mapBifunctorShift₁Iso P.obj (𝟙_ _) (curriedTensor C) n).hom) ≫
        ((L C).commShiftIso n).hom.app _ := by
  let : MonoidalCategory (CochainComplex C ℤ) := inferInstance
  let : MonoidalCategory (HomotopyCategory C (.up ℤ)) := inferInstance
  let : MonoidalCategory (DerivedCategory C) := inferInstance
  let a := ((CochainComplex.ιKFlat C).commShiftIso n).hom.app P
  have := Functor.CommShift₂OfLocalization.commShift_liftingIsoApp (M := ℤ) (L C) (LKFlat C)
    (HomologicalComplex.quasiIso C (.up ℤ)) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
    (F C).flip (curriedTensor (DerivedCategory C)).flip (𝟙_ _)
  have h₁ := NatTrans.shift_app_comm (Functor.CommShift₂OfLocalization.liftingIsoApp (L C)
    (LKFlat C) (HomologicalComplex.quasiIso C (.up ℤ))
    (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
    (F C).flip (curriedTensor (DerivedCategory C)).flip (𝟙_ _)) n P
  rw [Functor.commShiftIso_comp_hom_app] at h₁
  have h₂ := rightUnitor_shift_tensor_hom C P n
  have h₃ : ((LKFlat C).commShiftIso n).hom.app P =
      (L C).map a ≫ ((L C).commShiftIso n).hom.app P.obj :=
    Functor.commShiftIso_comp_hom_app _ _ _ _
  rw [h₂, h₃] at h₁
  simpa only [assoc] using h₁

open DerivedCategory.TensorCommShift₂ in
private lemma rightUnitor_shift (P : CochainComplex.KFlat C) (n : ℤ) :
    (((curriedTensor (DerivedCategory C)).flip.obj (𝟙_ _)).commShiftIso n).hom.app
        ((LKFlat C).obj P) ≫ (ρ_ ((LKFlat C).obj P)).hom⟦n⟧' =
      (ρ_ (((LKFlat C).obj P)⟦n⟧)).hom := by
  -- Reuse the tensor structures throughout the localization square.
  let : MonoidalCategory (CochainComplex C ℤ) := inferInstance
  let : MonoidalCategory (HomotopyCategory C (.up ℤ)) := inferInstance
  let : MonoidalCategory (DerivedCategory C) := inferInstance
  let : MonoidalCategoryStruct (CochainComplex C ℤ) := inferInstance
  let : MonoidalCategoryStruct (HomotopyCategory C (.up ℤ)) := inferInstance
  let : MonoidalCategoryStruct (DerivedCategory C) := inferInstance
  let a := ((CochainComplex.ιKFlat C).commShiftIso n).hom.app P
  have h₁ := rightUnitor_shift_lifting_square C P n
  have hr := rightUnitor_liftingIsoApp_hom C
  have hA : ((curriedTensor (DerivedCategory C)).flip.obj (𝟙_ _)).map
      ((L C).map (a) ≫
        ((L C).commShiftIso n).hom.app P.obj) ≫ (ρ_ (((LKFlat C).obj P)⟦n⟧)).hom =
      (ρ_ ((LKFlat C).obj (P⟦n⟧))).hom ≫
        (L C).map (a) ≫
          ((L C).commShiftIso n).hom.app P.obj :=
    rightUnitor_naturality _
  have hC : (ρ_ ((LKFlat C).obj P)).hom = (Functor.CommShift₂OfLocalization.liftingIsoApp
      (L C) (LKFlat C) (HomologicalComplex.quasiIso C (.up ℤ))
      (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat (F C).flip
      (curriedTensor (DerivedCategory C)).flip (𝟙_ _)).app P ≫
        (L C).map (ρ_ P.obj).hom :=
    (hr P).symm
  have hE := ((L C).commShiftIso_hom_naturality (ρ_ P.obj).hom n).symm
  have hF := CochainComplex.mapBifunctorShift₁Iso_hom_rightUnitor_hom P.obj n
  have hN := rightUnitor_naturality
    (a)
  rw [← cancel_epi (((curriedTensor (DerivedCategory C)).flip.obj (𝟙_ _)).map
      ((L C).map (a) ≫
        ((L C).commShiftIso n).hom.app P.obj)), hA]
  have hB := hr (P⟦n⟧)
  rw [← hB, hC, (shiftFunctor (DerivedCategory C) n).map_comp]
  erw [reassoc_of% h₁]
  rw [assoc]
  congr 1
  erw [hE]
  change (L C).map _ ≫ _ ≫ _ = _
  rw [← Functor.map_comp_assoc, assoc, hF]
  erw [hN]
  rw [Functor.map_comp_assoc]
  rfl

end DerivedCategory

private lemma rightUnitor_shift_of_iso
    {D : Type u} [Category.{v} D] [MonoidalCategory D] [HasShift D ℤ]
    [(tensorRight (𝟙_ D)).CommShift ℤ] {K K' : D} (e : K ≅ K') (n : ℤ)
    (h : ((tensorRight (𝟙_ D)).commShiftIso n).hom.app K ≫ (ρ_ K).hom⟦n⟧' =
      (ρ_ (K⟦n⟧)).hom) :
    ((tensorRight (𝟙_ D)).commShiftIso n).hom.app K' ≫ (ρ_ K').hom⟦n⟧' =
      (ρ_ (K'⟦n⟧)).hom ≫ ((𝟭 D).commShiftIso n).hom.app K' := by
  rw [Functor.commShiftIso_id_hom_app, comp_id]
  rw [← cancel_epi ((tensorRight (𝟙_ D)).map (e.hom⟦n⟧')),
    Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp]
  erw [rightUnitor_naturality]
  rw [Functor.map_comp, ← assoc, h]
  exact (rightUnitor_naturality (e.hom⟦n⟧')).symm

namespace DerivedCategory

variable (C : Type u) [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{s} C]
  [HasDerivedCategory.{v} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C] [HasColimitsOfSize.{0, 0} C]
  [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

attribute [local instance] commShift₂CurriedTensor

open DerivedCategory.TensorCommShift₂ in
private lemma rightUnitor_shift_all (K : DerivedCategory C) (n : ℤ) :
    ((tensorRight (𝟙_ (DerivedCategory C))).commShiftIso n).hom.app K ≫
        (ρ_ K).hom⟦n⟧' =
      (ρ_ (K⟦n⟧)).hom ≫ ((𝟭 (DerivedCategory C)).commShiftIso n).hom.app K := by
  let := Localization.essSurj (LKFlat C) (HomologicalComplex.quasiIso C (.up ℤ)).WKFlat
  exact rightUnitor_shift_of_iso ((LKFlat C).objObjPreimageIso K) n
    (rightUnitor_shift C ((LKFlat C).objPreimage K) n)

end DerivedCategory

namespace AlgebraicGeometry

/-- On a K-flat representative the canonical first-variable tensor shift commutes with
 the right unitor in degree one.
Source: Stacks Project, Tag 06YH, derived tensor localization;
WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift,
CochainComplex.mapBifunctorShift₁Iso_hom_rightUnitor_hom;
WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftUnitor,
DerivedCategory.rightUnitor_commShift (the same representative argument,
with an arbitrary K-flat first factor and independent universes).
(blueprint: lem-sc-scheme-canonical-tensor-shift-right-unitor).

Proof. Let U be the unit complex, concentrated in degree zero. For a K-flat P,
the tensor localization comparison Q(P) tensor Q(U) to Q(P tensor U) is invertible.
The derived right unitor at Q(P) is this comparison followed by the localization
of the complex right unitor, with the localization unit identification inserted.
This is the right-unit identity of the lax monoidal localization functor.
The defining shift square for the localized two-variable tensor comparison,
specialized to P and U, relates the derived first-variable shift to the complex
Koszul shift. In each summand of the total tensor complex with U, its second degree
is zero, so the Koszul sign for translation of the first variable is one.
Thus the complex right unitor commutes with that shift. Apply localization to
this equality and substitute the right-unit identity into the comparison square.
Naturality of the right unitor cancels the shift comparison for the inclusion of
K-flat complexes; naturality in the second variable absorbs the unit identification.
Cancel the invertible tensor localization comparison and localization shift maps.
The resulting equation is exactly the displayed square, with the usual shift of
the identity functor. All comparisons restrict to the unique morphism on zero
objects, so this also covers P zero and the empty scheme. -/
theorem schemeCanonicalTensorShift_rightUnitor (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    letI := schemeCanonicalTensorShift Y
    letI : ∀ M : schemeDerivedCategory Y, (tensorRight M).CommShift ℤ :=
      fun M ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) M
    ∀ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
      CochainComplex.IsKFlatTensor (R := Y.sheaf) P →
      let K := DerivedCategory.Q.obj P
      let τ := (rightUnitorNatIso (schemeDerivedCategory Y)).hom
      ((tensorRight (𝟙_ (schemeDerivedCategory Y))).commShiftIso (1 : ℤ)).hom.app K ≫
          (τ.app K)⟦(1 : ℤ)⟧' =
        τ.app (K⟦(1 : ℤ)⟧) ≫ ((𝟭 (schemeDerivedCategory Y)).commShiftIso
          (1 : ℤ)).hom.app K := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  let := SheafOfModules.symmetricCategory Y.sheaf
  have : MonoidalPreadditive (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed Y.sheaf).1
  let : MonoidalClosed (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed Y.sheaf).2.1
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  have : HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    hasColimitsOfSizeShrink.{0, 0, u, u} _
  have := schemeModule_hasFunctorialFlatResolution Y
  have := DerivedCategory.hasDerivedMonoidalCategory
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let := schemeCanonicalTensorShift Y
  let : ∀ M : schemeDerivedCategory Y, (tensorRight M).CommShift ℤ :=
    fun M ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) M
  intro P _
  exact DerivedCategory.rightUnitor_shift_all
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (DerivedCategory.Q.obj P) (1 : ℤ)

end AlgebraicGeometry
