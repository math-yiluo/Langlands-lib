/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveFirstSectionComparison
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveOrdinarySupportNormalization
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.RightDerivedSingleCounit

/-! # First-projection supported source normalization
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local implicit_reducible] firstProjection
attribute [local irreducible] CondensedRing.upperStar CondensedRing.lowerStar
  Functor.rightDerivedFunctor Functor.leftDerivedFunctor

universe a v w
private theorem canonical_model_single
    {A B : Type a} [Category.{v} A] [Category.{v} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (R : DiagonalRightDerived F)
    (e : R.R = F.rightDerivedFunctor) (he : IsCanonicalRightDerived F R e) (N : A) :
    diagonalTraceRightSingle F R N ≫
      (eqToIso e).hom.app ((DerivedCategory.singleFunctor A 0).obj N) =
      F.singleRightDerivedUnit.app N := by
  unfold diagonalTraceRightSingle
  dsimp only [CochainComplex.singleFunctor]
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp]
  have hu := he ((HomologicalComplex.single A (.up ℤ) 0).obj N)
  erw [R.R.map_id, Category.comp_id]
  erw [Category.assoc, hu]
  simp only [Functor.rightDerivedFunctorUnitQ, DerivedCategory.quotientCompQhIso,
    Functor.singleRightDerivedUnit_app,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  rfl
-- Fix the native module instances during support normalization.
private theorem first_ordinary_source
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L) :
    d.support₁.iso.inv =
      (CondensedRing.lowerStarComp Λ (diagonalImmersion Y) (firstProjection Y) ≪≫
        CondensedRing.lowerStarCongr Λ d.support₁.over_eq ≪≫
          CondensedRing.lowerStarId Λ (ProjectiveLine Y)).hom.app
            (Mod.regular (condensedRingObj Λ (ProjectiveLine Y))) := by
  exact ordinary_source_normalization Λ Y (firstProjection Y) d.support₁.iso
    d.support₁.over_eq d.support₁.normalization

private theorem ordinary_section_conjugate
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y)) :
    conjugateIsoEquiv Adjunction.id
      ((CondensedRing.upperStarLowerStarAdjunction Λ f).comp
        (CondensedRing.upperStarLowerStarAdjunction Λ (diagonalImmersion Y)))
      (ordinarySection Λ Y f h) =
      (CondensedRing.lowerStarComp Λ (diagonalImmersion Y) f ≪≫
        CondensedRing.lowerStarCongr Λ h ≪≫
          CondensedRing.lowerStarId Λ (ProjectiveLine Y)).symm := by
  unfold ordinarySection
  rw [conjugateIsoEquiv_trans Adjunction.id
      (CondensedRing.upperStarLowerStarAdjunction Λ (diagonalImmersion Y ≫ f)),
    conjugateIsoEquiv_trans Adjunction.id
      (CondensedRing.upperStarLowerStarAdjunction Λ (𝟙 (ProjectiveLine Y)))]
  simp only [conjugateIsoEquiv_iso_symm, CondensedRing.conjugateIsoEquiv_upperStarComp,
    CondensedRing.conjugateIsoEquiv_upperStarCongr,
    CondensedRing.conjugateIsoEquiv_upperStarId, Iso.trans_symm, Iso.trans_assoc]

private theorem canonical_diagram_single
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L) :
    diagonalTraceRightSingle (CondensedRing.lowerStar Λ (firstProjection Y)) d.R₁
        (source Λ Y) ≫
      (firstDiagramPushIso Λ Y L d).hom.app
        ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
          (source Λ Y)) =
      (CondensedRing.lowerStar Λ (firstProjection Y)).singleRightDerivedUnit.app
        (source Λ Y) := by
  unfold firstDiagramPushIso
  exact canonical_model_single _ d.R₁ d.p₁_canonical d.p₁_unit _

private theorem exact_single_unit_iso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (M : C) :
    F.singleRightDerivedUnit.app M ≫ F.singleFunctorCompRightDerivedFunctorIso.hom.app M =
      𝟙 _ := by
  have hu : F.singleRightDerivedUnit.app M ≫
      F.rightDerivedFunctorIsoMapDerivedCategory.hom.app
        ((DerivedCategory.singleFunctor C 0).obj M) =
      (F.mapDerivedCategorySingleFunctor 0).inv.app M := by
    rw [Functor.singleRightDerivedUnit_app]
    rw [Category.assoc]
    have hf := congr_app F.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
      ((HomotopyCategory.singleFunctor C 0).obj M)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
    erw [hf]
    have hh : F.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.singleFunctor C 0).obj M) =
        F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj M) := by
      change F.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient C (.up ℤ)).obj
          ((CochainComplex.singleFunctor C 0).obj M)) = _
      rw [Functor.mapDerivedCategoryFactorsh_hom_app]
      simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
      have hq (K : CochainComplex C ℤ) :
          (DerivedCategory.quotientCompQhIso C).hom.app K = 𝟙 _ := rfl
      have hqi (K : CochainComplex D ℤ) :
          (DerivedCategory.quotientCompQhIso D).inv.app K = 𝟙 _ := rfl
      simp only [hq, hqi, Functor.comp_obj]
      erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      simp only [Category.id_comp, Category.comp_id]
    apply (cancel_mono (F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.singleFunctor C 0).obj M))).1
    rw [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    rw [hh]
    exact (F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app M).symm
  simp only [Functor.singleFunctorCompRightDerivedFunctorIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  rw [← Category.assoc, hu, Iso.inv_hom_id_app]

/-- Cancel a split augmentation after applying a functor. -/
private theorem cancel_mapped_single_unit
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B : C} {P Q : D} (a : P ⟶ Q) (b : Q ⟶ F.obj A)
    (u : A ⟶ B) (v : B ⟶ A) (c : P ⟶ F.obj B)
    (h : a ≫ b ≫ F.map u = c) (hu : u ≫ v = 𝟙 A) :
    a ≫ b = c ≫ F.map v := by
  rw [← h, Category.assoc, Category.assoc, ← F.map_comp, hu, F.map_id,
    Category.comp_id]

-- Cancel the exact-single augmentation with fixed native functor instances.
/-- The normalized supported source agrees with the first-projection section arrow.
There is no variable tensor factor, kernel class, functional or outer direct image.
-/
theorem first_supported_source
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L) :
    d.support₁.hom ≫ (firstDiagramPushIso Λ Y L d).hom.app
        ((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
          (source Λ Y)) =
      (firstPushSectionIso Λ Y).hom.app (unit Λ (ProjectiveLine Y)) ≫
        (moduleObjectDerivedPushforward Λ (firstProjection Y)).map
          (supportedUnitIso Λ Y).hom := by
  have ho := ordinary_section_conjugate Λ Y (firstProjection Y) d.support₁.over_eq
  have hs := projective_section_single Λ Y (firstProjection Y) d.support₁.over_eq
    (Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))
  rw [ho] at hs
  have hn := first_ordinary_source Λ Y L d
  have hn' :
      ((CondensedRing.lowerStarComp Λ (diagonalImmersion Y) (firstProjection Y) ≪≫
        CondensedRing.lowerStarCongr Λ d.support₁.over_eq ≪≫
          CondensedRing.lowerStarId Λ (ProjectiveLine Y)).symm).hom.app
            (Mod.regular (condensedRingObj Λ (ProjectiveLine Y))) = d.support₁.iso.hom := by
    exact (Iso.inv_eq_inv
      ((CondensedRing.lowerStarComp Λ (diagonalImmersion Y) (firstProjection Y) ≪≫
        CondensedRing.lowerStarCongr Λ d.support₁.over_eq ≪≫
          CondensedRing.lowerStarId Λ (ProjectiveLine Y)).app
            (Mod.regular (condensedRingObj Λ (ProjectiveLine Y))))
      d.support₁.iso.symm).2 hn.symm
  rw [hn'] at hs
  have hi := exact_single_unit_iso
    (CondensedRing.lowerStar Λ (diagonalImmersion Y))
    (Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))
  have hc := cancel_mapped_single_unit
    (CondensedRing.lowerStar Λ (firstProjection Y)).rightDerivedFunctor
    _ _ _ _ _ hs hi
  dsimp only [DiagonalTrace.NormalizedSource.hom]
  change (_ ≫ diagonalTraceRightSingle
    (CondensedRing.lowerStar Λ (firstProjection Y)) d.R₁ (source Λ Y)) ≫ _ = _
  rw [Category.assoc, canonical_diagram_single]
  simpa only [derivedAdj, firstPushSectionIso, supportedUnitIso,
    moduleObjectDerivedPushforward, unit, source, id, Functor.id_obj, Iso.app_hom] using hc

end AlgebraicGeometry.ProEtale.RationalP1
