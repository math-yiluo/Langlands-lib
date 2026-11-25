/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalChernRealization
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientUnitPush
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence

/-! # Canonical derived coefficient-unit push -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u a v w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem ordinary_unit_endpoint
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (cF : UnitPullEndpoint Λ f) :
    (CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _
        (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).inv =
      (CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _ cF.iso.hom := by
  apply Mod.Hom.ext
  calc
    _ = condensedPushforwardHom Λ f := CondensedRing.homEquiv_εIso_inv_hom Λ f
    _ = _ := by
      simpa only [condensedPushforwardHom, Adjunction.unitAlgHom,
        Adjunction.homEquiv_unit] using! cF.normalization.symm

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor CondensedRing.upperStar CondensedRing.lowerStar

private theorem canonical_single_comparison
    {C B : Type a} [Category.{v} C] [Category.{v} B]
    [Abelian C] [Abelian B] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions C] (F : C ⥤ B) [F.Additive]
    (D : DiagonalRightDerived F) (e : D.R = F.rightDerivedFunctor)
    (h : IsCanonicalRightDerived F D e) (M : C) :
    singlePushComparison D M ≫
        (eqToIso e).hom.app ((DerivedCategory.singleFunctor C 0).obj M) =
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) ≫
        F.rightDerivedFunctorUnitQ ((HomologicalComplex.single C (.up ℤ) 0).obj M) := by
  unfold singlePushComparison
  rw [Category.assoc]
  exact congrArg (fun k ↦ DerivedCategory.Q.map
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) ≫ k)
      (h ((HomologicalComplex.single C (.up ℤ) 0).obj M))

private theorem cochain_unit_normalization_generic
    {C B : Type a} [Category.{v} C] [Category.{v} B]
    [Abelian C] [Abelian B] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} B]
    [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).obj X)]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution C]
    [Abelian.HasKInjectiveResolutions B]
    {L : C ⥤ B} {R : B ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (a : L ⊣ R) (P : CochainComplex C ℤ) :
    a.derivedAdjunction.unit.app (DerivedCategory.Q.obj P) ≫
        R.rightDerivedFunctor.map
          (L.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj P) ≫
            L.mapDerivedCategoryFactors.hom.app P) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        R.rightDerivedFunctorUnitQ ((L.mapHomologicalComplex (.up ℤ)).obj P) := by
  have h := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ)) L.leftDerivedFunctorCounit
    R.rightDerivedFunctorUnit
    ((HomotopyCategory.quotient C (.up ℤ)).obj P)
  change a.derivedAdjunction.unit.app _ ≫
    R.rightDerivedFunctor.map (L.leftDerivedFunctorCounit.app _) = _ at h
  have hf := congr_app L.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((HomotopyCategory.quotient C (.up ℤ)).obj P)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
  rw [← hf] at h
  simp only [Functor.rightDerivedFunctorUnitQ, Functor.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_unit_app_quotient,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.map_comp, Quotient.lift.isLift_hom] at h ⊢
  erw [L.mapDerivedCategory.map_id, R.rightDerivedFunctor.map_id,
    DerivedCategory.Qh.map_id, R.rightDerivedFunctor.map_id] at h
  erw [R.rightDerivedFunctor.map_id]
  repeat erw [Category.id_comp]
  repeat erw [Category.comp_id]
  simpa only [Category.id_comp, Category.comp_id] using! h

-- The cochain comparison elaborates concrete derived-category instances.
private theorem cochain_unit_normalization
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (P : CochainComplex (Modules Λ S) ℤ) :
    let L := CondensedRing.upperStar Λ f
    let R := CondensedRing.lowerStar Λ f
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).unit.app
        (DerivedCategory.Q.obj P) ≫
        R.rightDerivedFunctor.map
          (L.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj P) ≫
            L.mapDerivedCategoryFactors.hom.app P) =
      DerivedCategory.Q.map
          (((CondensedRing.upperStarLowerStarAdjunction Λ f).mapHomologicalComplex
            (.up ℤ)).unit.app P) ≫
        R.rightDerivedFunctorUnitQ ((L.mapHomologicalComplex (.up ℤ)).obj P) := by
  let L := CondensedRing.upperStar Λ f
  let R := CondensedRing.lowerStar Λ f
  let a := CondensedRing.upperStarLowerStarAdjunction Λ f
  exact cochain_unit_normalization_generic a P

-- Single comparisons share the concrete inverse-image and derived-category instances.
private theorem adjunct_single
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Modules Λ S) (N : Modules Λ X)
    (c : (CondensedRing.upperStar Λ f).obj M ⟶ N) :
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).homEquiv _ _
        ((singlePullback Λ f M).hom ≫ (DerivedCategory.singleFunctor _ 0).map c) =
      (DerivedCategory.singleFunctor _ 0).map
          ((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _ c) ≫
        DerivedCategory.Q.map
          (((CondensedRing.lowerStar Λ f).mapCochainComplexSingleFunctor 0).inv.app N) ≫
        (CondensedRing.lowerStar Λ f).rightDerivedFunctorUnitQ
          ((CochainComplex.singleFunctor _ 0).obj N) := by
  let L := CondensedRing.upperStar Λ f
  let R := CondensedRing.lowerStar Λ f
  let adj := CondensedRing.upperStarLowerStarAdjunction Λ f
  let P := (CochainComplex.singleFunctor (Modules Λ S) 0).obj M
  let t := (L.mapCochainComplexSingleFunctor 0).hom.app M ≫
    (CochainComplex.singleFunctor (Modules Λ X) 0).map c
  have hc : (adj.mapHomologicalComplex (.up ℤ)).unit.app P ≫
      (R.mapHomologicalComplex (.up ℤ)).map t =
    (CochainComplex.singleFunctor (Modules Λ S) 0).map (adj.homEquiv _ _ c) ≫
      (R.mapCochainComplexSingleFunctor 0).inv.app N := by
    apply HomologicalComplex.Hom.ext
    funext i
    by_cases hi : i = 0
    · subst i
      suffices h : adj.unit.app M ≫ R.map (𝟙 (L.obj M)) ≫ R.map c =
          adj.unit.app M ≫ R.map c ≫ 𝟙 _ by
        simpa [R, P, t, Functor.mapCochainComplexSingleFunctor,
          CochainComplex.singleFunctor, CochainComplex.singleFunctors,
          HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
          HomologicalComplex.single, Adjunction.homEquiv_unit] using! h
      erw [R.map_id, Category.id_comp]
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi).eq_of_src _ _
  have hu := cochain_unit_normalization Λ f P
  have hn := R.rightDerivedFunctorUnitQ_naturality t
  rw [Adjunction.homEquiv_unit]
  unfold singlePullback
  simp only [Iso.app_hom, Functor.singleFunctorCompLeftDerivedFunctorIso,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerLeft_app]
  erw [L.mapDerivedCategorySingleFunctor_hom_app_eq]
  calc
    _ = ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).unit.app
          (DerivedCategory.Q.obj P) ≫ R.rightDerivedFunctor.map
            (L.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj P) ≫
              L.mapDerivedCategoryFactors.hom.app P)) ≫
        R.rightDerivedFunctor.map (DerivedCategory.Q.map t) := by
      simp only [t, Functor.map_comp, Category.assoc]
      rfl
    _ = DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        R.rightDerivedFunctorUnitQ ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
        R.rightDerivedFunctor.map (DerivedCategory.Q.map t) := by rw [hu, Category.assoc]
    _ = DerivedCategory.Q.map
          ((adj.mapHomologicalComplex (.up ℤ)).unit.app P ≫
            (R.mapHomologicalComplex (.up ℤ)).map t) ≫
        R.rightDerivedFunctorUnitQ ((CochainComplex.singleFunctor (Modules Λ X) 0).obj N) := by
      erw [← hn]
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [hc, Functor.map_comp, Category.assoc]
      rfl

-- Abstract coefficients keep the derived comparison independent of ring realizations.
private theorem canonical_unit_push_general
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (D : DiagonalRightDerived (CondensedRing.lowerStar Λ f))
    (canonical : D.R = derivedLower Λ f)
    (hcanonical : IsCanonicalRightDerived (CondensedRing.lowerStar Λ f) D canonical)
    (cF : UnitPullEndpoint Λ f)
    (T : DerivedCategory (Modules Λ X)) (q : unit Λ X ⟶ T) :
    let a := (CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _
      (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).inv
    let unitPush := (DerivedCategory.singleFunctor _ 0).map a ≫
      singlePushComparison D (Mod.regular (condensedRingObj Λ X))
    unitPush ≫ D.R.map q = modelLocalAdjunct Λ f D canonical cF q := by
  apply (cancel_mono ((eqToIso canonical).hom.app T)).mp
  have hn := (eqToIso canonical).hom.naturality q
  simp only [Category.assoc]
  erw [hn]
  erw [reassoc_of% canonical_single_comparison _ D canonical hcanonical]
  erw [ordinary_unit_endpoint Λ f cF]
  have hs := adjunct_single Λ f _ _ cF.iso.hom
  unfold modelLocalAdjunct
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [← reassoc_of% hs]
  erw [Category.comp_id]
  simpa only [PullEndpoint.derived, derivedLower] using!
    ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).homEquiv_naturality_right
      cF.derived q).symm

-- The concrete coefficient specialization can require substantial kernel conversion.
/-- The single condensed coefficient-unit push is the canonical derived
adjunction unit after the chosen endpoint and right-derived identifications.

Source: diagonal coefficient pullback endpoints and the universal right-derived
unit normalization.
(blueprint: lem-diagonal-canonical-unit-push).

Proof: expand `singlePushComparison`, use the canonical right-derived equation
on the single complex, and use the normalized endpoint to identify the
ordinary monoidal-unit adjunct. The resulting mate is exactly
`modelLocalAdjunct` after the canonical equality.
-/
theorem diagonalCanonicalUnitPush (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} [DiagonalTraceLocalizations l X]
    [DiagonalTraceLocalizations l S]
    (f : X ⟶ S)
    (D : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f))
    (canonical : D.R = derivedLower (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (hcanonical : IsCanonicalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f) D canonical)
    (cF : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (T : DerivedCategory (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X))
    (q : unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) X ⟶ T) :
    let Λ := Profinite.continuousMapRingObj.{u} ℤ_[l]
    let a := (CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _
      (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).inv
    let unitPush := (DerivedCategory.singleFunctor _ 0).map a ≫
      singlePushComparison D (Mod.regular (condensedRingObj Λ X))
    unitPush ≫ D.R.map q = modelLocalAdjunct Λ f D canonical cF q := by
  exact @canonical_unit_push_general _ _ _ X S f D canonical hcanonical cF T q

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
