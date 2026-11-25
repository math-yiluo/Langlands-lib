/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicFiniteDiagramData
import all WeilConjectures.CategoryTheory.Exact.ExactScalarMatePasting
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import all WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import all WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import all WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import all Mathlib.CategoryTheory.Filtered.Basic
import all Mathlib.CategoryTheory.Limits.Cones
import all WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Functor.Derived.Adjunction
import all Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import all WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Adjunction.CompositionIso
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientData

/-! # The actual adic tower after restriction to constant completion coefficients

Source: Stacks Project, Tags 03DA and 06YY, scalar restriction and its compositors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem restrictComp_apply
    {T : Scheme.{u}} {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (h : a ≫ b = c)
    (M : pbcModules T B) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrictComp a b c h).hom.app M).val.app U x = x :=
  (pbcRestrictComp_exists a b c h).exists.choose_spec M U x

private theorem restrictComp_inv_apply
    {T : Scheme.{u}} {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (h : a ≫ b = c)
    (M : pbcModules T B) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrictComp a b c h).inv.app M).val.app U x = x := by
  have hh := congrArg (fun t ↦ t.val.app U x)
    ((pbcRestrictComp a b c h).inv_hom_id_app M)
  simpa only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply, restrictComp_apply, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply] using hh

attribute [local instance] proEtaleRingRestrictionPullbackInv_isIso

private def scalarPullSquare {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :=
  asIso (proEtaleRingRestrictionPullbackInv g R S
    ((adicTowerInverseImage g).obj R) ((adicTowerInverseImage g).obj S)
    a ((adicTowerInverseImage g).map a) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm))

private def scalarDirectSquare {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :=
  proEtaleRingRestrictionDirectImage g R S
    ((adicTowerInverseImage g).obj R) ((adicTowerInverseImage g).obj S)
    a ((adicTowerInverseImage g).map a) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)

private theorem scalarDirectSquare_apply {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (M : pbcModules Y ((adicTowerInverseImage g).obj S)) (U : X.ProEtᵒᵖ)
    (x : M.val.obj ((proEtaleBaseChange g).op.obj U)) :
    ((scalarDirectSquare g a).hom.app M).val.app U x = x :=
  (proEtaleRingRestrictionDirectImage_existsUnique g R S
    ((adicTowerInverseImage g).obj R) ((adicTowerInverseImage g).obj S)
    a ((adicTowerInverseImage g).map a) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)).choose_spec.1 M U x

private theorem scalarPullSquare_mate {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :
    (mateEquiv
      (proEtaleRingModuleAdjunction g S ((adicTowerInverseImage g).obj S) (Iso.refl _))
      (proEtaleRingModuleAdjunction g R ((adicTowerInverseImage g).obj R) (Iso.refl _))
      (TwoSquare.mk _ _ _ _ (scalarPullSquare g a).hom)) =
        (scalarDirectSquare g a).hom :=
  restrictionPullback_mate g R S
    ((adicTowerInverseImage g).obj R) ((adicTowerInverseImage g).obj S)
    a ((adicTowerInverseImage g).map a) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)

private theorem scalarPullSquare_comp {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (h : a ≫ b = c) :
    let hi := ((adicTowerInverseImage g).map_comp a b).symm.trans
      (congrArg (adicTowerInverseImage g).map h)
    ∀ M : pbcModules X B,
      (proEtaleRingModulePullback g R ((adicTowerInverseImage g).obj R)
        (Iso.refl _)).map ((pbcRestrictComp a b c h).hom.app M) ≫
          (scalarPullSquare g c).hom.app M =
        (scalarPullSquare g a).hom.app ((pbcRestrict b).obj M) ≫
          (pbcRestrict ((adicTowerInverseImage g).map a)).map
            ((scalarPullSquare g b).hom.app M) ≫
          (pbcRestrictComp ((adicTowerInverseImage g).map a)
            ((adicTowerInverseImage g).map b) ((adicTowerInverseImage g).map c)
              hi).hom.app
                ((proEtaleRingModulePullback g B ((adicTowerInverseImage g).obj B)
                  (Iso.refl _)).obj M) := by
  dsimp only
  let hi := ((adicTowerInverseImage g).map_comp a b).symm.trans
    (congrArg (adicTowerInverseImage g).map h)
  let adj (T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
    proEtaleRingModuleAdjunction g T ((adicTowerInverseImage g).obj T) (Iso.refl _)
  let t := TwoSquare.hComp
    (TwoSquare.mk _ _ _ _ (scalarPullSquare g b).hom)
    (TwoSquare.mk _ _ _ _ (scalarPullSquare g a).hom)
  let t' := (t.whiskerTop (pbcRestrictComp a b c h).inv).whiskerBottom
    (pbcRestrictComp ((adicTowerInverseImage g).map a)
      ((adicTowerInverseImage g).map b) ((adicTowerInverseImage g).map c) hi).hom
  have ht : (mateEquiv (adj B) (adj R) t') =
      (scalarDirectSquare g c).hom := by
    rw [mate_whisker]
    have hh := mateEquiv_vcomp (adj B) (adj S) (adj R)
      (TwoSquare.mk _ _ _ _ (scalarPullSquare g b).hom)
      (TwoSquare.mk _ _ _ _ (scalarPullSquare g a).hom)
    change (mateEquiv (adj B) (adj R) t) = _ at hh
    have hm (T T' : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (k : T ⟶ T') :
        (mateEquiv (adj T') (adj T))
          (TwoSquare.mk _ _ _ _ (scalarPullSquare g k).hom) =
            TwoSquare.mk _ _ _ _ (scalarDirectSquare g k).hom := by
      refine NatTrans.ext (funext fun N ↦ ?_)
      exact congr_app (scalarPullSquare_mate g k) N
    rw [hm S B b, hm R S a] at hh
    rw [hh]
    ext M U x
    change ((pbcRestrictComp ((adicTowerInverseImage g).map a)
        ((adicTowerInverseImage g).map b) ((adicTowerInverseImage g).map c) hi).hom.app M
          ).val.app ((proEtaleBaseChange g).op.obj U)
      (((scalarDirectSquare g a).hom.app
        ((pbcRestrict ((adicTowerInverseImage g).map b)).obj M)).val.app U
        (((scalarDirectSquare g b).hom.app M).val.app U
          (((pbcRestrictComp a b c h).inv.app _).val.app U x))) =
        ((scalarDirectSquare g c).hom.app M).val.app U x
    rw [restrictComp_apply, scalarDirectSquare_apply, scalarDirectSquare_apply,
      restrictComp_inv_apply, scalarDirectSquare_apply]
  have ht' : t' = TwoSquare.mk _ _ _ _ (scalarPullSquare g c).hom := by
    apply (mateEquiv (adj B) (adj R)).injective
    refine NatTrans.ext (funext fun M ↦ ?_)
    exact congr_app (ht.trans (scalarPullSquare_mate g c).symm) M
  intro M
  have hh := congrArg (fun k ↦ k.app M) (ht')
  apply (cancel_epi ((proEtaleRingModulePullback g R
    ((adicTowerInverseImage g).obj R) (Iso.refl _)).map
      ((pbcRestrictComp a b c h).inv.app M))).mp
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  simpa only [t', t, TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id] using hh.symm

private def scalarDerivedSquare {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :
    pbcDerivedRestrict a ⋙ adicTowerPullback g R ≅
      adicTowerPullback g S ⋙ pbcDerivedRestrict ((adicTowerInverseImage g).map a) :=
  Functor.mapDerivedCategorySquareIso (scalarPullSquare g a)

private theorem scalarDerivedSquare_eq {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :
    scalarDerivedSquare g a =
      (proEtaleRingRestrictionDerivedPullback g R S
        ((adicTowerInverseImage g).obj R) ((adicTowerInverseImage g).obj S)
        a ((adicTowerInverseImage g).map a) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans (Category.comp_id _).symm)).symm := by
  apply Iso.ext
  simp only [scalarDerivedSquare, Functor.mapDerivedCategorySquareIso,
    proEtaleRingRestrictionDerivedPullback, scalarPullSquare, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, ← Functor.mapDerivedCategoryNatIso_symm,
    Iso.symm_symm_eq, Category.assoc]

private theorem scalarDerivedSquare_hom {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S) :
    (scalarDerivedSquare g a).hom =
      (proEtaleRingRestrictionDerivedPullback g R S
        ((adicTowerInverseImage g).obj R) ((adicTowerInverseImage g).obj S)
        a ((adicTowerInverseImage g).map a) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans (Category.comp_id _).symm)).inv :=
  congrArg (fun e ↦ e.hom) (scalarDerivedSquare_eq g a)

private theorem scalarDerivedSquare_comp {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (h : a ≫ b = c)
    (M : DerivedCategory (pbcModules X B)) :
    let hi := ((adicTowerInverseImage g).map_comp a b).symm.trans
      (congrArg (adicTowerInverseImage g).map h)
    (adicTowerPullback g R).map ((pbcDerivedRestrictComp a b c h).hom.app M) ≫
        (scalarDerivedSquare g c).hom.app M =
      (scalarDerivedSquare g a).hom.app ((pbcDerivedRestrict b).obj M) ≫
        (pbcDerivedRestrict ((adicTowerInverseImage g).map a)).map
          ((scalarDerivedSquare g b).hom.app M) ≫
        (pbcDerivedRestrictComp ((adicTowerInverseImage g).map a)
          ((adicTowerInverseImage g).map b) ((adicTowerInverseImage g).map c) hi).hom.app
            ((adicTowerPullback g B).obj M) := by
  dsimp only
  let hi := ((adicTowerInverseImage g).map_comp a b).symm.trans
    (congrArg (adicTowerInverseImage g).map h)
  have ho (N : pbcModules X B) :
      (proEtaleRingModulePullback g R ((adicTowerInverseImage g).obj R)
        (Iso.refl _)).map ((pbcRestrictComp a b c h).inv.app N) ≫
          (scalarPullSquare g a).hom.app ((pbcRestrict b).obj N) ≫
            (pbcRestrict ((adicTowerInverseImage g).map a)).map
              ((scalarPullSquare g b).hom.app N) =
        (scalarPullSquare g c).hom.app N ≫
          (pbcRestrictComp ((adicTowerInverseImage g).map a)
            ((adicTowerInverseImage g).map b) ((adicTowerInverseImage g).map c) hi).inv.app
              ((proEtaleRingModulePullback g B ((adicTowerInverseImage g).obj B)
                (Iso.refl _)).obj N) := by
    have hh := scalarPullSquare_comp g a b c h N
    have hh' := congrArg (fun k ↦
      (proEtaleRingModulePullback g R ((adicTowerInverseImage g).obj R)
        (Iso.refl _)).map ((pbcRestrictComp a b c h).inv.app N) ≫ k ≫
          (pbcRestrictComp ((adicTowerInverseImage g).map a)
            ((adicTowerInverseImage g).map b) ((adicTowerInverseImage g).map c) hi).inv.app
              ((proEtaleRingModulePullback g B ((adicTowerInverseImage g).obj B)
                (Iso.refl _)).obj N)) hh
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app] at hh'
    erw [Category.comp_id] at hh'
    exact hh'.symm
  have hd := Functor.exactSquare_comp_forward
    (pbcRestrict b) (pbcRestrict a) (pbcRestrict c)
    (pbcRestrict ((adicTowerInverseImage g).map b))
    (pbcRestrict ((adicTowerInverseImage g).map a))
    (pbcRestrict ((adicTowerInverseImage g).map c))
    (proEtaleRingModulePullback g B ((adicTowerInverseImage g).obj B) (Iso.refl _))
    (proEtaleRingModulePullback g S ((adicTowerInverseImage g).obj S) (Iso.refl _))
    (proEtaleRingModulePullback g R ((adicTowerInverseImage g).obj R) (Iso.refl _))
    (scalarPullSquare g b) (scalarPullSquare g a) (scalarPullSquare g c)
    (pbcRestrictComp a b c h).symm
    (pbcRestrictComp ((adicTowerInverseImage g).map a)
      ((adicTowerInverseImage g).map b) ((adicTowerInverseImage g).map c) hi).symm ho M
  have hX : (Functor.mapDerivedCategoryNatIso (pbcRestrictComp a b c h).symm ≪≫
      (Functor.mapDerivedCategoryCompIso (pbcRestrict b) (pbcRestrict a)).symm).hom =
        (pbcDerivedRestrictComp a b c h).inv := by
    simp only [pbcDerivedRestrictComp, Functor.mapDerivedCategoryNatIso_symm,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom]
  have hY : (Functor.mapDerivedCategoryNatIso
      (pbcRestrictComp ((adicTowerInverseImage g).map a)
        ((adicTowerInverseImage g).map b) ((adicTowerInverseImage g).map c) hi).symm ≪≫
      (Functor.mapDerivedCategoryCompIso
        (pbcRestrict ((adicTowerInverseImage g).map b))
        (pbcRestrict ((adicTowerInverseImage g).map a))).symm).hom =
      (pbcDerivedRestrictComp ((adicTowerInverseImage g).map a)
        ((adicTowerInverseImage g).map b) ((adicTowerInverseImage g).map c) hi).inv := by
    simp only [pbcDerivedRestrictComp, Functor.mapDerivedCategoryNatIso_symm,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom]
  rw [hX, hY] at hd
  have hh := congrArg (fun k ↦
    (adicTowerPullback g R).map ((pbcDerivedRestrictComp a b c h).hom.app M) ≫ k ≫
      (pbcDerivedRestrictComp ((adicTowerInverseImage g).map a)
        ((adicTowerInverseImage g).map b) ((adicTowerInverseImage g).map c) hi).hom.app
          ((adicTowerPullback g B).obj M)) hd
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app] at hh
  erw [Category.comp_id] at hh
  exact hh.symm

private theorem derivedRestrictComp_assoc
    {T : Scheme.{u}} {R S B V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : B ⟶ V)
    (ab : R ⟶ B) (bc : S ⟶ V) (abc : R ⟶ V)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (habc : ab ≫ c = abc) (habc' : a ≫ bc = abc) :
    Functor.isoWhiskerLeft (pbcDerivedRestrict c) (pbcDerivedRestrictComp a b ab hab) ≪≫
        pbcDerivedRestrictComp ab c abc habc =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (pbcDerivedRestrictComp b c bc hbc) (pbcDerivedRestrict a) ≪≫
        pbcDerivedRestrictComp a bc abc habc' := by
  apply SheafOfModules.SuccessiveDerivedQuotient.exactComp_assoc
  apply Iso.ext
  ext M U x
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp]
  change ((pbcRestrictComp ab c abc habc).hom.app M).val.app U
      (((pbcRestrictComp a b ab hab).hom.app ((pbcRestrict c).obj M)).val.app U x) =
    ((pbcRestrictComp a bc abc habc').hom.app M).val.app U
      (((pbcRestrictComp b c bc hbc).hom.app M).val.app U x)
  simp only [restrictComp_apply]

private theorem pulledTransition_comp {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower X d) (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    let q (m n : ℕ) (h : n ≤ m) := pbcAdicQuotient X d m n h
    let hi := ((adicTowerInverseImage g).map_comp (q c b hbc) (q b a hab)).symm.trans
      (congrArg (adicTowerInverseImage g).map (pbcAdicQuotient_comp X d c b a hab hbc))
    adicTowerRestrictedTransition d g M c a (hab.trans hbc) =
      adicTowerRestrictedTransition d g M c b hbc ≫
        (pbcDerivedRestrict ((adicTowerInverseImage g).map (q c b hbc))).map
          (adicTowerRestrictedTransition d g M b a hab) ≫
        (pbcDerivedRestrictComp ((adicTowerInverseImage g).map (q c b hbc))
          ((adicTowerInverseImage g).map (q b a hab))
          ((adicTowerInverseImage g).map (q c a (hab.trans hbc))) hi).hom.app
            ((adicTowerPullback g ((pbcAdicRings X d).obj (op a))).obj (M.level a)) := by
  dsimp only
  let q (m n : ℕ) (h : n ≤ m) := pbcAdicQuotient X d m n h
  let v (m n : ℕ) (h : n ≤ m) :=
    adicTowerSemilinearTransition X d M.level M.normalization m n h
  have hs := scalarDerivedSquare_comp g (q c b hbc) (q b a hab)
    (q c a (hab.trans hbc)) (pbcAdicQuotient_comp X d c b a hab hbc) (M.level a)
  have hn := (scalarDerivedSquare g (q c b hbc)).hom.naturality (v b a hab)
  change (adicTowerPullback g ((pbcAdicRings X d).obj (op c))).map
      ((pbcDerivedRestrict (q c b hbc)).map (v b a hab)) ≫
        (scalarDerivedSquare g (q c b hbc)).hom.app
          ((pbcDerivedRestrict (q b a hab)).obj (M.level a)) =
    (scalarDerivedSquare g (q c b hbc)).hom.app (M.level b) ≫
      (pbcDerivedRestrict ((adicTowerInverseImage g).map (q c b hbc))).map
        ((adicTowerPullback g ((pbcAdicRings X d).obj (op b))).map (v b a hab)) at hn
  simp only [adicTowerRestrictedTransition, ← scalarDerivedSquare_hom]
  rw [M.cocycle c b a hab hbc]
  simp only [Functor.map_comp, Category.assoc]
  rw [hs, reassoc_of% hn]

private def actualCommonTransition {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower X d) (m n : ℕ) (h : n ≤ m) :
    (pbcDerivedRestrict (constantAdicFiniteProjection g d m)).obj
        ((adicTowerPullback g ((pbcAdicRings X d).obj (op m))).obj (M.level m)) ⟶
      (pbcDerivedRestrict (constantAdicFiniteProjection g d n)).obj
        ((adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj (M.level n)) :=
  (pbcDerivedRestrict (constantAdicFiniteProjection g d m)).map
      (adicTowerRestrictedTransition d g M m n h) ≫
    (pbcDerivedRestrictComp (constantAdicFiniteProjection g d m)
      ((adicTowerInverseImage g).map (pbcAdicQuotient X d m n h))
      (constantAdicFiniteProjection g d n)
      (constantAdicFiniteProjection_comp g d m n h)).hom.app
        ((adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj (M.level n))

private theorem actualCommonTransition_comp {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower X d) (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    actualCommonTransition g d M c a (hab.trans hbc) =
      actualCommonTransition g d M c b hbc ≫ actualCommonTransition g d M b a hab := by
  let p (n : ℕ) := constantAdicFiniteProjection g d n
  let q (m n : ℕ) (h : n ≤ m) :=
    (adicTowerInverseImage g).map (pbcAdicQuotient X d m n h)
  let hc := ((adicTowerInverseImage g).map_comp
    (pbcAdicQuotient X d c b hbc) (pbcAdicQuotient X d b a hab)).symm.trans
      (congrArg (adicTowerInverseImage g).map (pbcAdicQuotient_comp X d c b a hab hbc))
  have hs := congrArg (fun e ↦ e.hom.app
      ((adicTowerPullback g ((pbcAdicRings X d).obj (op a))).obj (M.level a)))
    (derivedRestrictComp_assoc (p c) (q c b hbc) (q b a hab) (p b)
      (q c a (hab.trans hbc)) (p a)
      (constantAdicFiniteProjection_comp g d c b hbc) hc
      (constantAdicFiniteProjection_comp g d b a hab)
      (constantAdicFiniteProjection_comp g d c a (hab.trans hbc)))
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] at hs
  have hn := (pbcDerivedRestrictComp (p c) (q c b hbc) (p b)
    (constantAdicFiniteProjection_comp g d c b hbc)).hom.naturality
      (adicTowerRestrictedTransition d g M b a hab)
  dsimp only [Functor.comp_map] at hn
  dsimp only [actualCommonTransition]
  rw [pulledTransition_comp g d M c b a hab hbc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← hs, reassoc_of% hn]

private theorem towerTransition_id (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (n : ℕ) :
    pbcTowerTransition X R n n le_rfl = 𝟙 (pbcTowerEvaluation X R n) := by
  unfold pbcTowerTransition
  have hi : (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X R)).map
      (homOfLE (le_refl n)).op =
        𝟙 ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X R)).obj (op n)) := by
    simp
  rw [hi, NatTrans.mapHomologicalComplex_id]
  have hw : Functor.whiskerRight
      (𝟙 (((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X R)).obj (op n)).mapHomologicalComplex
        (.up ℤ))) DerivedCategory.Q = 𝟙 _ := by
    ext K
    simp
  rw [hw, Localization.liftNatTrans_id]

private theorem semilinearTransition_id_isIso {X : Scheme.{u}}
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower X d) (n : ℕ) :
    IsIso (adicTowerSemilinearTransition X d M.level M.normalization n n le_rfl) := by
  let a := pbcAdicProjection X d n
  have := (proEtaleRingRestrictScalars_properties a).2.2
  have : (pbcDerivedRestrict a).ReflectsIsomorphisms := by
    refine ⟨fun k hk ↦ ?_⟩
    have : IsIso ((pbcRestrict a).mapDerivedCategory.map k) := hk
    rw [DerivedCategory.isIso_iff]
    intro q
    have : IsIso ((pbcRestrict a).map ((DerivedCategory.homologyFunctor _ q).map k)) :=
      (NatIso.isIso_map_iff ((pbcRestrict a).mapDerivedCategoryHomologyFunctorIso q) k).2
        (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ (pbcRestrict a)
  let v := adicTowerSemilinearTransition X d M.level M.normalization n n le_rfl
  let e := (pbcDerivedRestrictComp a (pbcAdicQuotient X d n n le_rfl) a
    (pbcAdicProjection_comp X d n n le_rfl)).hom.app (M.level n) ≫ (M.evaluation n).hom
  have h : (pbcDerivedRestrict a).map v ≫ e = (M.evaluation n).hom := by
    simpa only [Category.assoc, towerTransition_id, NatTrans.id_app, Category.comp_id]
      using M.transition n n le_rfl
  have : IsIso ((pbcDerivedRestrict a).map v ≫ e) := by
    rw [h]
    infer_instance
  have : IsIso ((pbcDerivedRestrict a).map v) := IsIso.of_isIso_comp_right _ e
  exact isIso_of_reflects_iso v (pbcDerivedRestrict a)

private theorem actualCommonTransition_id {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower X d) (n : ℕ) :
    actualCommonTransition g d M n n le_rfl = 𝟙 _ := by
  have := semilinearTransition_id_isIso d M n
  have : IsIso (actualCommonTransition g d M n n le_rfl) := by
    dsimp only [actualCommonTransition, adicTowerRestrictedTransition]
    infer_instance
  apply (cancel_epi (actualCommonTransition g d M n n le_rfl)).mp
  simpa only [Category.comp_id] using
    (actualCommonTransition_comp g d M n n n le_rfl le_rfl).symm

/-- The consecutive actual transitions, restricted to the common constant coefficient ring.
Source: Stacks Tags 03DA and 06YY.
(blueprint: lem-weil-pbc-constant-adic-restricted-tower-maps). -/
def constantAdicRestrictedStep {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower X d) (n : ℕ) :=
  (pbcDerivedRestrict (constantAdicFiniteProjection g d (n + 1))).map
      (adicTowerRestrictedTransition d g M (n + 1) n (Nat.le_succ n)) ≫
    (pbcDerivedRestrictComp (constantAdicFiniteProjection g d (n + 1))
      ((adicTowerInverseImage g).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
      (constantAdicFiniteProjection g d n)
      (constantAdicFiniteProjection_comp g d (n + 1) n (Nat.le_succ n))).hom.app
        ((adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj (M.level n))

/-- The sequential diagram built from the actual consecutive transitions.
Source: Stacks Tags 03DA and 06YY.
(blueprint: lem-weil-pbc-constant-adic-restricted-tower-maps). -/
def constantAdicRestrictedTower {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower X d) :
    ℕᵒᵖ ⥤ DerivedCategory (pbcModules Y ((adicTowerInverseImage g).obj
      (adicLisseConstantRing X (AdicCompletion d.ideal A)))) :=
  Functor.ofOpSequence (X := fun n ↦
    (pbcDerivedRestrict (constantAdicFiniteProjection g d n)).obj
      ((adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj (M.level n)))
    (constantAdicRestrictedStep g d M)

/-- Composing consecutive transitions recovers every actual normalized transition.
No local systems, bounds, stalk models, markings or covering are used.

Source: Stacks Tags 03DA and 06YY; the semilinear cocycle in
`def-weil-pbc-bounded-constructible-tower`.
(blueprint: lem-weil-pbc-constant-adic-restricted-tower-maps).

Proof: scalar restriction compositors are identity on underlying sections, so their
associativity is checked sectionwise. The inverse-image/scalar-restriction comparisons
are the mates of the corresponding identity squares and preserve this pasting identity.
Apply exact derived localization to both identities. Apply these identities to M.cocycle
and use naturality of the compositors: the displayed restricted all-pairs arrows compose.
For equal indices M.transition identifies the arrow, after restriction along the completed
projection, with the identity of the derived evaluation. Exact scalar restriction
reflects isomorphisms, as checked on homology. Thus the equal-index arrow is invertible.
Its cocycle makes it idempotent, so cancellation gives the identity. The same pasting
identity gives identity after restriction to the constant ring. Induction on the
difference of the indices now identifies the actual arrow with the arrow of the
sequential diagram; the successor case is its defining step. -/
theorem constantAdicRestrictedTower_map {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower X d) (m n : ℕ) (h : n ≤ m) :
    (constantAdicRestrictedTower g d M).map (homOfLE h).op =
      (pbcDerivedRestrict (constantAdicFiniteProjection g d m)).map
          (adicTowerRestrictedTransition d g M m n h) ≫
        (pbcDerivedRestrictComp (constantAdicFiniteProjection g d m)
          ((adicTowerInverseImage g).map (pbcAdicQuotient X d m n h))
          (constantAdicFiniteProjection g d n)
          (constantAdicFiniteProjection_comp g d m n h)).hom.app
            ((adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj
              (M.level n)) := by
  change (constantAdicRestrictedTower g d M).map (homOfLE h).op =
    actualCommonTransition g d M m n h
  induction m, h using Nat.le_induction with
  | base =>
      have hi : (homOfLE (le_refl n)).op = 𝟙 (op n) := Subsingleton.elim _ _
      rw [hi, CategoryTheory.Functor.map_id, actualCommonTransition_id]
      rfl
  | succ m h ih =>
      have hc : (homOfLE (h.trans (Nat.le_succ m))).op =
          (homOfLE (Nat.le_succ m)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
      rw [hc, Functor.map_comp, ih]
      have he : (constantAdicRestrictedTower g d M).map
          (homOfLE (Nat.le_succ m)).op = constantAdicRestrictedStep g d M m := by
        exact Functor.ofOpSequence_map_homOfLE_succ _ _
      rw [he]
      exact (actualCommonTransition_comp g d M (m + 1) m n h (Nat.le_succ m)).symm

end AlgebraicGeometry.Scheme
