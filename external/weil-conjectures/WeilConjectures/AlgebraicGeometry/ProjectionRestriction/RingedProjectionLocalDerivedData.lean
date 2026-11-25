/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionLocalBaseData
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionOrdinarySliceMate
import WeilConjectures.CategoryTheory.UnboundedExactTower.UnboundedExactAdjunctionSquare
import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-! Derived comparison data for localized projection sites.

## References

* Stacks Project, Cohomology on Sites, Tags 08FI and 0FN5
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.ProjectionRestriction

/-- The derived comparison portion of localized projection data.

The structure contains the normalized direct-image and pullback comparisons,
their representative equations, and the counit mate equation.  The restriction
and tensor package is supplied separately by `LocalBaseData`. -/
structure LocalDerivedData {X Y : Scheme.{u}} {f : X ⟶ Y}
    {R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X}
    (g : Global f R_Y R_X c) (V : Y.ProEt)
    (b : LocalBaseData g V) where
  [restrictionYAdditive : (SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y) V).Additive]
  [restrictionXAdditive : (SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
      ((proEtaleBaseChange f).obj V)).Additive]
  [leftRouteZero : (g.operation.pushforward ⋙
    SheafOfModules.overFunctor.{u + 1}
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y) V).PreservesZeroMorphisms]
  [rightRouteZero : (SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
      ((proEtaleBaseChange f).obj V) ⋙ b.operation.pushforward).PreservesZeroMorphisms]
  ordinaryDirectImage : g.operation.pushforward ⋙
      SheafOfModules.overFunctor.{u + 1}
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y) V ≅
    SheafOfModules.overFunctor.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
        ((proEtaleBaseChange f).obj V) ⋙ b.operation.pushforward
  ordinaryDirectImage_sections : ∀ (M : Mod R_X) (T : (Over V)ᵒᵖ)
      (x : M.val.obj (op ((proEtaleBaseChange f).obj T.unop.left))),
    ((ordinaryDirectImage.hom.app M).val.app T) x = x
  restrictsKInjective : ∀ I : CochainComplex (Mod R_X) ℤ, I.IsKInjective →
    CochainComplex.IsKInjective ((SheafOfModules.overFunctor.{u + 1}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
      ((proEtaleBaseChange f).obj V)).mapHomologicalComplex (.up ℤ) |>.obj I)
  directImage : g.operation.right ⋙ (b.restrictionY.model).functor ≅
    (b.restrictionX.model).functor ⋙ b.operation.right
  directImage_shift : NatTrans.CommShift directImage.hom ℤ
  directImage_representative : ∀ (I : CochainComplex (Mod R_X) ℤ), I.IsKInjective →
    b.restrictionY.model.functor.map (g.operation.rightComparison I) ≫
      directImage.hom.app (DerivedCategory.Q.obj I) =
    b.restrictionY.model.factors.hom.app
        ((g.operation.pushforward.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinaryDirectImage (.up ℤ)).hom.app I) ≫
      b.operation.rightComparison ((SheafOfModules.overFunctor.{u + 1}
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
          ((proEtaleBaseChange f).obj V)).mapHomologicalComplex (.up ℤ) |>.obj I) ≫
      b.operation.right.map (b.restrictionX.model.factors.inv.app I)
  pullback : g.operation.left ⋙ (b.restrictionX.model).functor ≅
    (b.restrictionY.model).functor ⋙ b.operation.left
  pullback_shift : NatTrans.CommShift pullback.hom ℤ
  mate_counit : ∀ E : Der R_X,
    b.operation.left.map (directImage.hom.app E) ≫
      b.operation.derivedCounit.app (b.restrictionX.model.functor.obj E) =
    pullback.inv.app (g.operation.right.obj E) ≫
      b.restrictionX.model.functor.map (g.operation.derivedCounit.app E)

private theorem rightComparison_isIso
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}
    (o : Operation F R S) (I : CochainComplex (Mod S) ℤ) [I.IsKInjective] :
    IsIso (o.rightComparison I) := by
  let := o.kInjectives
  dsimp only [Operation.rightComparison, derivedPushforwardComplexComparison]
  infer_instance

attribute [local instance] Limits.comp_preservesFiniteLimits Limits.comp_preservesFiniteColimits

-- Elaborate the canonical derived mate and its two localized coefficient models.
/-- The derived comparison package exists for every base package. -/
theorem localDerivedData_exists {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X)
    (g : Global f R_Y R_X c) (V : Y.ProEt) (b : LocalBaseData g V) :
    Nonempty (LocalDerivedData g V b) := by
  let := b.restrictionYAdditive
  let := b.restrictionXAdditive
  let := b.operation.continuous
  let := g.operation.continuous
  let r := SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y) V
  let t := SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
      ((proEtaleBaseChange f).obj V)
  let : r.Additive := b.restrictionYAdditive
  let : t.Additive := b.restrictionXAdditive
  let : g.operation.pushforward.Additive := g.operation.pushforwardAdditive
  let : b.operation.pushforward.Additive := b.operation.pushforwardAdditive
  let : g.operation.pullback.Additive := g.operation.pullbackAdditive
  let : b.operation.pullback.Additive := b.operation.pullbackAdditive
  let : Limits.PreservesFiniteLimits g.operation.pullback := g.operation.pullbackLimits
  let : Limits.PreservesFiniteColimits g.operation.pullback := g.operation.pullbackColimits
  let : Limits.PreservesFiniteLimits b.operation.pullback := b.operation.pullbackLimits
  let : Limits.PreservesFiniteColimits b.operation.pullback := b.operation.pullbackColimits
  let : (g.operation.pushforward ⋙ r).PreservesZeroMorphisms :=
    { map_zero := by intro A B; change r.map (g.operation.pushforward.map 0) = 0; simp }
  let : (t ⋙ b.operation.pushforward).PreservesZeroMorphisms :=
    { map_zero := by intro A B; change b.operation.pushforward.map (t.map 0) = 0; simp }
  have ht : ∀ I : CochainComplex (Mod R_X) ℤ, I.IsKInjective →
      CochainComplex.IsKInjective ((t.mapHomologicalComplex (.up ℤ)).obj I) := by
    intro I hI
    let := hI
    exact CategoryTheory.isKInjective_restrict_localizedOfUniverses.{u + 1, u, u + 1}
      _ _ inferInstance I
  let ordinary : g.operation.pushforward ⋙ r ≅ t ⋙ b.operation.pushforward :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (show ((g.operation.pushforward ⋙ r).obj M).val ≅
          ((t ⋙ b.operation.pushforward).obj M).val from
        PresheafOfModules.isoMk (fun T ↦
          (ModuleCat.restrictScalarsCongr
            (congrArg RingCat.Hom.hom (b.coefficient_sections T.unop)).symm).app
              (M.val.obj (op ((proEtaleBaseChange f).obj T.unop.left))))
          (by intros; ext; rfl))) (by intros; ext; rfl)
  have hsections : ∀ (M : Mod R_X) (T : (Over V)ᵒᵖ)
      (x : M.val.obj (op ((proEtaleBaseChange f).obj T.unop.left))),
      ((ordinary.hom.app M).val.app T) x = x := by
    intros
    rfl
  let := b.restrictionY.limits
  let := b.restrictionY.colimits
  let := b.restrictionX.limits
  let := b.restrictionX.colimits
  let := g.operation.kInjectives
  let := b.operation.kInjectives
  have := localOrdinaryInverseMate_isIso g V b ordinary hsections
  let theta := asIso (((mateEquiv g.operation.moduleAdjunction
    b.operation.moduleAdjunction).symm (TwoSquare.mk _ _ _ _ ordinary.hom)))
  have htheta : (mateEquiv g.operation.moduleAdjunction b.operation.moduleAdjunction
      (TwoSquare.mk _ _ _ _ theta.hom)) = ordinary.hom := by
    exact
      ((mateEquiv g.operation.moduleAdjunction b.operation.moduleAdjunction).apply_symm_apply
        (TwoSquare.mk _ _ _ _ ordinary.hom))
  let thetaD := CategoryTheory.UnboundedExactTower.localizedSquare
    g.operation.pullback b.operation.pullback r t theta
  let beta := (mateEquiv g.operation.derivedAdjunction b.operation.derivedAdjunction
    (TwoSquare.mk _ _ _ _ thetaD.hom))
  have hnormal (I : CochainComplex (Mod R_X) ℤ) :
      r.mapDerivedCategoryFactors.inv.app
          ((g.operation.pushforward.mapHomologicalComplex (.up ℤ)).obj I) ≫
        r.mapDerivedCategory.map (g.operation.rightComparison I) ≫
        beta.app (DerivedCategory.Q.obj I) ≫
        b.operation.right.map (t.mapDerivedCategoryFactors.hom.app I) =
      DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app I) ≫
        b.operation.rightComparison ((t.mapHomologicalComplex (.up ℤ)).obj I) := by
    have hn := CategoryTheory.UnboundedExactTower.localized_mate_cochain_normalization
      g.operation.moduleAdjunction b.operation.moduleAdjunction theta I
    rw [htheta] at hn
    exact hn
  have hcompute (I : CochainComplex (Mod R_X) ℤ) :
      r.mapDerivedCategory.map (g.operation.rightComparison I) ≫
        beta.app (DerivedCategory.Q.obj I) =
      r.mapDerivedCategoryFactors.hom.app
          ((g.operation.pushforward.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app I) ≫
        b.operation.rightComparison ((t.mapHomologicalComplex (.up ℤ)).obj I) ≫
        b.operation.right.map (t.mapDerivedCategoryFactors.inv.app I) := by
    have hn := congrArg (fun z ↦
      r.mapDerivedCategoryFactors.hom.app
        ((g.operation.pushforward.mapHomologicalComplex (.up ℤ)).obj I) ≫ z ≫
      b.operation.right.map (t.mapDerivedCategoryFactors.inv.app I)) (hnormal I)
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
      Iso.hom_inv_id_app] at hn
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at hn
    exact hn
  have hbetaI (I : CochainComplex (Mod R_X) ℤ) (hI : I.IsKInjective) :
      IsIso (beta.app (DerivedCategory.Q.obj I)) := by
    let := hI
    let := ht I hI
    have := rightComparison_isIso g.operation I
    have := rightComparison_isIso b.operation ((t.mapHomologicalComplex (.up ℤ)).obj I)
    have : IsIso (r.mapDerivedCategory.map (g.operation.rightComparison I) ≫
        beta.app (DerivedCategory.Q.obj I)) := by
      rw [hcompute I]
      infer_instance
    exact IsIso.of_isIso_comp_left (r.mapDerivedCategory.map (g.operation.rightComparison I)) _
  have : IsIso beta := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro E
    obtain ⟨I, hI, s, _, hs⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
      (DerivedCategory.Q.objPreimage E)
    let := hs
    let e : E ≅ DerivedCategory.Q.obj I :=
      (DerivedCategory.Q.objObjPreimageIso E).symm ≪≫ asIso (DerivedCategory.Q.map s)
    have := hbetaI I hI
    have he : beta.app E =
        (g.operation.right ⋙ r.mapDerivedCategory).map e.hom ≫
          beta.app (DerivedCategory.Q.obj I) ≫
          (t.mapDerivedCategory ⋙ b.operation.right).map e.inv := by
      rw [beta.naturality_assoc, ← Functor.map_comp, Iso.hom_inv_id]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
    rw [he]
    infer_instance
  let : g.operation.derivedAdjunction.CommShift ℤ :=
    CategoryTheory.canonicalRightDerivedAdjunctionShift g.operation.moduleAdjunction
  let : b.operation.derivedAdjunction.CommShift ℤ :=
    CategoryTheory.canonicalRightDerivedAdjunctionShift b.operation.moduleAdjunction
  have hthetaD : NatTrans.CommShift thetaD.hom ℤ := by
    dsimp only [thetaD, CategoryTheory.UnboundedExactTower.localizedSquare,
      Iso.trans_hom, Iso.symm_hom]
    let : NatTrans.CommShift (r.mapDerivedCategoryCompIso b.operation.pullback).inv ℤ :=
      NatTrans.CommShift.of_iso_inv _ ℤ
    infer_instance
  let := hthetaD
  have hbeta : NatTrans.CommShift beta ℤ :=
    NatTrans.CommShift.mateEquiv g.operation.derivedAdjunction b.operation.derivedAdjunction _
  refine ⟨{
    restrictionYAdditive := b.restrictionYAdditive
    restrictionXAdditive := b.restrictionXAdditive
    leftRouteZero := inferInstance
    rightRouteZero := inferInstance
    ordinaryDirectImage := ordinary
    ordinaryDirectImage_sections := hsections
    restrictsKInjective := ht
    directImage := asIso beta
    directImage_shift := hbeta
    directImage_representative := fun I _ ↦ hcompute I
    pullback := thetaD.symm
    pullback_shift := NatTrans.CommShift.of_iso_inv thetaD ℤ
    mate_counit := ?_ }⟩
  intro E
  exact mateEquiv_counit g.operation.derivedAdjunction b.operation.derivedAdjunction
    (TwoSquare.mk _ _ _ _ thetaD.hom) E

end AlgebraicGeometry.Scheme.ProjectionRestriction
