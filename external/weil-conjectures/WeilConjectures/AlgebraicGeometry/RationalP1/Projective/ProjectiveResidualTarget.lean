/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparison
public import WeilConjectures.CategoryTheory.Right.RightDerivedSingleH0
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveSectionSingle
import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectiveSupportedNormalization
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits

private theorem exact_single_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (M : C) :
    F.singleRightDerivedUnit.app M = F.singleFunctorCompRightDerivedFunctorIso.inv.app M := by
  have hu : F.singleRightDerivedUnit.app M ≫
      F.rightDerivedFunctorIsoMapDerivedCategory.hom.app
        ((DerivedCategory.singleFunctor C 0).obj M) =
      (F.mapDerivedCategorySingleFunctor 0).inv.app M := by
    rw [Functor.singleRightDerivedUnit_app]
    erw [Category.assoc]
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
      change F.mapDerivedCategory.map (𝟙 (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor C 0).obj M))) ≫
        F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj M) ≫
        𝟙 (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj
          ((CochainComplex.singleFunctor C 0).obj M))) ≫
        DerivedCategory.Qh.map (𝟙 ((HomotopyCategory.quotient D (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj
            ((CochainComplex.singleFunctor C 0).obj M)))) = _
      erw [F.mapDerivedCategory.map_id, (DerivedCategory.Qh (C := D)).map_id]
      change 𝟙 _ ≫ F.mapDerivedCategoryFactors.hom.app
        ((CochainComplex.singleFunctor C 0).obj M) ≫ 𝟙 _ ≫ 𝟙 _ = _
      simp only [Category.id_comp, Category.comp_id]
    apply (cancel_mono (F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.singleFunctor C 0).obj M))).1
    erw [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    erw [hh]
    exact (F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app M).symm
  apply (cancel_mono (F.singleFunctorCompRightDerivedFunctorIso.hom.app M)).1
  simp only [Iso.inv_hom_id_app]
  change F.singleRightDerivedUnit.app M ≫
    F.rightDerivedFunctorIsoMapDerivedCategory.hom.app _ ≫
      (F.mapDerivedCategorySingleFunctor 0).hom.app M = _
  erw [← Category.assoc, hu, Iso.inv_hom_id_app]

private theorem section_cancel
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ E) (G : D ⥤ E) {X Y : C} {Z W : D}
    (a : X ≅ Y) (b : Z ≅ W) (u : F.obj Y ⟶ G.obj Z) (v : F.obj X ⟶ G.obj W)
    (h : F.map a.hom ≫ u ≫ G.map b.hom = v) :
    u = F.map a.inv ≫ v ≫ G.map b.inv := by
  apply (Iso.eq_inv_comp (F.mapIso a)).2
  apply (Iso.eq_comp_inv (G.mapIso b)).2
  simpa only [CategoryTheory.Functor.mapIso_hom, Category.assoc] using h

set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
attribute [local irreducible] CondensedRing.upperStar CondensedRing.lowerStar

private theorem ordinary_section_conjugate (Y : Scheme.{u})
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
  rw [conjugateIsoEquiv_trans _
    (CondensedRing.upperStarLowerStarAdjunction Λ (diagonalImmersion Y ≫ f)) _]
  rw [conjugateIsoEquiv_trans _
    (CondensedRing.upperStarLowerStarAdjunction Λ (𝟙 (ProjectiveLine Y))) _]
  simp only [CondensedRing.conjugateIsoEquiv_upperStarId,
    CondensedRing.conjugateIsoEquiv_upperStarCongr, conjugateIsoEquiv_iso_symm,
    CondensedRing.conjugateIsoEquiv_upperStarComp]
  simp only [Iso.trans_symm, Iso.trans_assoc]

private theorem ordinary_second_section (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L) :
    (conjugateIsoEquiv Adjunction.id
      ((CondensedRing.upperStarLowerStarAdjunction Λ (secondProjection Y)).comp
        (CondensedRing.upperStarLowerStarAdjunction Λ (diagonalImmersion Y)))
      (ordinarySection Λ Y (secondProjection Y) d.support₂.over_eq)).hom.app
        (Mod.regular (condensedRingObj Λ (ProjectiveLine Y))) = d.support₂.iso.hom := by
  have hn := projective_supported_normalization Λ Y L d
  rw [ordinary_section_conjugate Λ Y (secondProjection Y) d.support₂.over_eq]
  apply (cancel_mono d.support₂.iso.inv).1
  rw [Iso.hom_inv_id, hn]
  exact Iso.inv_hom_id_app _ _

private theorem diagonal_single_unit (Y : Scheme.{u}) :
    (CondensedRing.lowerStar Λ (diagonalImmersion Y)).singleRightDerivedUnit.app
        (Mod.regular (condensedRingObj Λ (ProjectiveLine Y))) =
      (supportedUnitIso Λ Y).inv := by
  exact exact_single_unit (CondensedRing.lowerStar Λ (diagonalImmersion Y)) _

private theorem second_section_single (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L) :
    (DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).map
      d.support₂.iso.hom ≫
    (CondensedRing.lowerStar Λ (secondProjection Y)).singleRightDerivedUnit.app
      (source Λ Y) ≫
    (moduleObjectDerivedPushforward Λ (secondProjection Y)).map (supportedUnitIso Λ Y).inv =
    (pushSectionIso Λ Y).hom.app (unit Λ (ProjectiveLine Y)) := by
  have hs := projective_section_single Λ Y (secondProjection Y) d.support₂.over_eq
    (Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))
  rw [ordinary_second_section Λ Y L d, diagonal_single_unit Λ Y] at hs
  exact hs

/- Residual section and support comparison after the diagram unit is identified. -/
theorem projective_residual_target (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L) :
    (CondensedRing.lowerStar Λ (secondProjection Y)).singleRightDerivedUnit.app
        (source Λ Y) =
      (DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).map
          d.support₂.iso.inv ≫
        (pushSectionIso Λ Y).hom.app (unit Λ (ProjectiveLine Y)) ≫
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
        (supportedUnitIso Λ Y).hom := by
  exact section_cancel (DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0)
    (moduleObjectDerivedPushforward Λ (secondProjection Y)) d.support₂.iso
    (supportedUnitIso Λ Y).symm _ _ (second_section_single Λ Y L d)
end AlgebraicGeometry.ProEtale.RationalP1
