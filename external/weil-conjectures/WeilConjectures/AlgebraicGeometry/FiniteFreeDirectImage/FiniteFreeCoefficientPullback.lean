/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageData
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
import all WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
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
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
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
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import all Mathlib.CategoryTheory.Sites.Pullback
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import all Mathlib.Algebra.Category.Grp.Colimits
import all WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import all WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleTensorCompositionUnit
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import all Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence

/-! # Pullback of a finite free coefficient module

Source: Stacks Project, Tags 03D2, 03D3 and 03EL.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.FiniteFreeDirectImage

attribute [local instance] proEtaleRingRestrictionPullbackInv_isIso

private def inverseRegularIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    (proEtaleModuleInverseImage f R).obj (SheafOfModules.unit ((sheafCompose
      (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ≅
    SheafOfModules.unit ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)) := by
  let : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsEquivalence
  have : PreservesFiniteLimits (proEtaleModelBaseChange f) := by
    dsimp only [proEtaleModelBaseChange]
    infer_instance
  have : (proEtaleModelBaseChange f).Final := inferInstance
  exact (proEtaleModuleFromModel _).mapIso
    (asIso (SheafOfModules.pullbackObjUnitToUnit (proEtaleModelRingUnit f R)))

private def pullbackRegularIso {Z W : Scheme.{u}} {q : Z ⟶ W} (R : Coefficients q) :
    (proEtaleRingModulePullback q R.target R.source R.identification).obj
      (SheafOfModules.unit ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.target)) ≅
    SheafOfModules.unit ((sheafCompose (ProEt.topology Z)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.source) :=
  (proEtaleRingExtension q R.target R.source R.identification).mapIso
    (inverseRegularIso q R.target) ≪≫
    SheafOfModules.comparisonUnitIso R.identification.hom

private theorem inverseRegularIso_sections {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (V : Y.ProEt) (r : R.obj.obj (Opposite.op V)) :
    (inverseRegularIso f R).hom.val.app (Opposite.op ((proEtaleBaseChange f).obj V))
      (((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit f R)).unit.app
        ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj
          (SheafOfModules.unit _))).val.app (Opposite.op (AsSmall.up.obj V)) r) =
    ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app (Opposite.op V) r := by
  let φ := proEtaleModelRingUnit f R
  have h := ((SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv _ _).apply_symm_apply
    (SheafOfModules.unitToPushforwardObjUnit φ)
  have h' := congrArg (fun k ↦ k.val.app (Opposite.op (AsSmall.up.obj V)) r) h
  change _ = _ at h'
  exact h'

private theorem pullbackRegularIso_unit {Z W : Scheme.{u}} {q : Z ⟶ W}
    (R : Coefficients q) (V : W.ProEt) (r : R.target.obj.obj (Opposite.op V)) :
    (pullbackRegularIso R).hom.val.app (Opposite.op ((proEtaleBaseChange q).obj V))
      (((proEtaleRingModuleAdjunction q R.target R.source R.identification).unit.app
        (SheafOfModules.unit ((sheafCompose (ProEt.topology W)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.target))).val.app
            (Opposite.op V) r) =
    (proEtaleRingDirectImageMap q R.target R.source R.identification).hom.app
      (Opposite.op V) r := by
  let U := Opposite.op ((proEtaleBaseChange q).obj V)
  let M := (proEtaleModuleInverseImage q R.target).obj
    (SheafOfModules.unit ((sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.target))
  let x : M.val.obj U :=
    (((SheafOfModules.pullbackPushforwardAdjunction
      (proEtaleModelRingUnit q R.target)).unit.app
        ((proEtaleModuleToModel ((sheafCompose (ProEt.topology W)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.target)).obj
            (SheafOfModules.unit _))).val.app (Opposite.op (AsSmall.up.obj V)) r)
  rw [canonicalAdjunction_normalized]
  change (SheafOfModules.comparisonUnitIso R.identification.hom).hom.val.app U
    ((SheafOfModules.changeOfRingsHomOfUniverses R.identification.hom M
      (inverseRegularIso q R.target).hom).val.app U
        (SheafOfModules.scalarExtensionSection R.identification.hom M U 1 x)) = _
  have hmap := SheafOfModules.scalarExtension_map_tmul R.identification.hom
    (inverseRegularIso q R.target).hom U 1 x
  refine (congrArg (fun t ↦
    (SheafOfModules.comparisonUnitIso R.identification.hom).hom.val.app U t) hmap).trans ?_
  change (SheafOfModules.unitForward R.identification.hom).val.app U
    (SheafOfModules.scalarExtensionConstraintTmul R.identification.hom _ U
      ((inverseRegularIso q R.target).hom.val.app U x) 1) = _
  refine (SheafOfModules.unitForward_tmul R.identification.hom U 1 _).trans ?_
  refine (one_mul (R.identification.hom.hom.app U
    ((inverseRegularIso q R.target).hom.val.app U x))).trans ?_
  exact congrArg (fun t ↦ R.identification.hom.hom.app U t)
    (inverseRegularIso_sections q R.target V r)

private def transportedCoefficientBasis {Z W : Scheme.{u}} {q : Z ⟶ W}
    (R S : Coefficients q) (a : CoefficientMap R S) (d : ℕ)
    (θ : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.target)) ≅
      (proEtaleRingRestrictScalars a.target).obj (SheafOfModules.unit ((sheafCompose
        (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.target))) :
    (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((sheafCompose (ProEt.topology Z)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.source)) ≅
      (proEtaleRingRestrictScalars a.source).obj (SheafOfModules.unit ((sheafCompose
        (ProEt.topology Z) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.source)) :=
  Pi.mapIso (fun _ : Fin d ↦ (pullbackRegularIso R).symm) ≪≫
    (PreservesProduct.iso
      (proEtaleRingModulePullback q R.target R.source R.identification)
      (fun _ : Fin d ↦ SheafOfModules.unit ((sheafCompose (ProEt.topology W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.target))).symm ≪≫
    (proEtaleRingModulePullback q R.target R.source R.identification).mapIso θ ≪≫
    (asIso (proEtaleRingRestrictionPullbackInv q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm)).app
        (SheafOfModules.unit ((sheafCompose (ProEt.topology W)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.target)) ≪≫
    (proEtaleRingRestrictScalars a.source).mapIso (pullbackRegularIso S)

-- Compute the coordinate before specializing to the geometric pullback functors.
private theorem transportedBasisCoordinate {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {ι : Type*} (O : C) (O' : D)
    [HasProduct (fun _ : ι ↦ O)] [HasProductsOfShape ι D]
    [PreservesLimit (Discrete.functor (fun _ : ι ↦ O)) F]
    {A : C} {B B' : D} (e : F.obj O ≅ O')
    (θ : (∏ᶜ fun _ : ι ↦ O) ≅ A) (ρ : F.obj A ≅ B) (σ : B ≅ B') (i : ι) :
    F.map (θ.inv ≫ Pi.π _ i) ≫ e.hom =
      ρ.hom ≫ σ.hom ≫
        (Pi.mapIso (fun _ : ι ↦ e.symm) ≪≫
          (PreservesProduct.iso F (fun _ : ι ↦ O)).symm ≪≫ F.mapIso θ ≪≫ ρ ≪≫ σ).inv ≫
        Pi.π _ i := by
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc,
    Iso.hom_inv_id_assoc, Pi.mapIso_inv_π, PreservesProduct.iso_hom,
    piComparison_comp_π_assoc, Functor.map_comp]

private theorem transportedCoefficientBasis_coordinate {Z W : Scheme.{u}} {q : Z ⟶ W}
    (R S : Coefficients q) (a : CoefficientMap R S) (d : ℕ)
    (θ : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.target)) ≅
      (proEtaleRingRestrictScalars a.target).obj (SheafOfModules.unit ((sheafCompose
        (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.target)))
    (i : Fin d) :
    (proEtaleRingModulePullback q R.target R.source R.identification).map
      (θ.inv ≫ Pi.π _ i) ≫ (pullbackRegularIso R).hom =
    (proEtaleRingRestrictionPullbackInv q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm).app
        (SheafOfModules.unit ((sheafCompose (ProEt.topology W)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.target)) ≫
      (proEtaleRingRestrictScalars a.source).map (pullbackRegularIso S).hom ≫
      (transportedCoefficientBasis R S a d θ).inv ≫ Pi.π _ i := by
  exact transportedBasisCoordinate
    (proEtaleRingModulePullback q R.target R.source R.identification) _ _
    (pullbackRegularIso R) θ
    ((asIso (proEtaleRingRestrictionPullbackInv q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm)).app _)
    ((proEtaleRingRestrictScalars a.source).mapIso (pullbackRegularIso S)) i

private theorem restrictionPullback_unit {Z W : Scheme.{u}} {q : Z ⟶ W}
    (R S : Coefficients q) (a : CoefficientMap R S)
    (N : proEtaleRingModules W S.target) (V : W.ProEtᵒᵖ) (n : N.val.obj V) :
    ((proEtaleRingRestrictionPullbackInv q R.target S.target R.source S.source
      a.target a.source R.identification S.identification a.comm).app N).val.app
        ((proEtaleBaseChange q).op.obj V)
          (((proEtaleRingModuleAdjunction q R.target R.source R.identification).unit.app
            ((proEtaleRingRestrictScalars a.target).obj N)).val.app V n) =
    (((proEtaleRingModuleAdjunction q S.target S.source S.identification).unit.app N).val.app
      V n) := by
  let adjR := proEtaleRingModuleAdjunction q R.target R.source R.identification
  let adjS := proEtaleRingModuleAdjunction q S.target S.source S.identification
  let ρ := proEtaleRingRestrictionPullbackInv q R.target S.target R.source S.source
    a.target a.source R.identification S.identification a.comm
  let d := proEtaleRingRestrictionDirectImage q R.target S.target R.source S.source
    a.target a.source R.identification S.identification a.comm
  have h := unit_mateEquiv adjS adjR (TwoSquare.mk _ _ _ _ ρ) N
  have hm := restrictionPullback_mate q R.target S.target R.source S.source
    a.target a.source R.identification S.identification a.comm
  change (proEtaleRingRestrictScalars a.target).map (adjS.unit.app N) ≫
    (mateEquiv adjS adjR (TwoSquare.mk _ _ _ _ ρ)).app _ = _ at h
  rw [hm] at h
  have hh := congrArg (fun f ↦ f.val.app V n) h
  have hd := (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique q
    R.target S.target R.source S.source a.target a.source
    R.identification S.identification a.comm)).1
      ((proEtaleRingModulePullback q S.target S.source S.identification).obj N) V
      ((adjS.unit.app N).val.app V n)
  exact hh.symm.trans hd

private theorem basisCoordinate_unit {Z W : Scheme.{u}} {q : Z ⟶ W}
    (R S : Coefficients q) (a : CoefficientMap R S) (d : ℕ)
    (θ : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.target)) ≅
      (proEtaleRingRestrictScalars a.target).obj (SheafOfModules.unit ((sheafCompose
        (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.target)))
    (V : W.ProEtᵒᵖ) (b : S.target.obj.obj V) (i : Fin d) :
    ((transportedCoefficientBasis R S a d θ).inv ≫ Pi.π _ i).val.app
      ((proEtaleBaseChange q).op.obj V)
      ((proEtaleRingDirectImageMap q S.target S.source S.identification).hom.app V b) =
    (proEtaleRingDirectImageMap q R.target R.source R.identification).hom.app V
      ((θ.inv ≫ Pi.π _ i).val.app V b) := by
  let c := θ.inv ≫ Pi.π _ i
  let cZ := (transportedCoefficientBasis R S a d θ).inv ≫ Pi.π _ i
  let F := proEtaleRingModulePullback q R.target R.source R.identification
  let adjR := proEtaleRingModuleAdjunction q R.target R.source R.identification
  let adjS := proEtaleRingModuleAdjunction q S.target S.source S.identification
  let OS : proEtaleRingModules W S.target := SheafOfModules.unit _
  let ρ := proEtaleRingRestrictionPullbackInv q R.target S.target R.source S.source
    a.target a.source R.identification S.identification a.comm
  let VZ := (proEtaleBaseChange q).op.obj V
  have h := congrArg (fun f ↦ f.val.app VZ
    ((adjR.unit.app ((proEtaleRingRestrictScalars a.target).obj OS)).val.app V b))
      (transportedCoefficientBasis_coordinate R S a d θ i)
  change (pullbackRegularIso R).hom.val.app VZ
    ((F.map c).val.app VZ ((adjR.unit.app _).val.app V b)) =
    cZ.val.app VZ ((pullbackRegularIso S).hom.val.app VZ
      ((ρ.app OS).val.app VZ ((adjR.unit.app _).val.app V b))) at h
  have hn := congrArg (fun f ↦ f.val.app V b) (adjR.unit.naturality c)
  change (adjR.unit.app _).val.app V (c.val.app V b) =
    (F.map c).val.app VZ ((adjR.unit.app _).val.app V b) at hn
  have hL := pullbackRegularIso_unit R V.unop (c.val.app V b)
  have hR := congrArg (fun t ↦ cZ.val.app VZ
    ((pullbackRegularIso S).hom.val.app VZ t)) (restrictionPullback_unit R S a OS V b)
  have hS := congrArg (fun t ↦ cZ.val.app VZ t) (pullbackRegularIso_unit S V.unop b)
  exact (hR.trans hS).symm.trans (h.symm.trans
    ((congrArg (fun t ↦ (pullbackRegularIso R).hom.val.app VZ t) hn.symm).trans hL))

/-- The pulled-back coefficient basis has the expected coordinate formula.
Source: Stacks Project, Tags 03D2, 03D3 and 03EL.
(blueprint: lem-sp-finite-free-coefficient-pullback).

Proof: identify inverse image of each regular module with the source regular module
using the model-site pullback unit and scalar multiplication. Transport the given
basis through finite-product preservation, the restriction/pullback comparison and
these regular-module identifications. Cancel the comparison and basis isomorphisms
to compute each projection. Evaluate on the geometric adjunction unit; its naturality
and normalization give the displayed coefficient formula, including rank zero. -/
theorem finiteFreeDirectImage_coefficientPullback {Z W : Scheme.{u}} {q : Z ⟶ W}
    (R S : Coefficients q) (a : CoefficientMap R S) (d : ℕ)
    (θ : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.target)) ≅
      (proEtaleRingRestrictScalars a.target).obj (SheafOfModules.unit ((sheafCompose
        (ProEt.topology W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.target))) :
    ∃ θZ : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((sheafCompose (ProEt.topology Z)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R.source)) ≅
      (proEtaleRingRestrictScalars a.source).obj (SheafOfModules.unit ((sheafCompose
        (ProEt.topology Z) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S.source)),
    ∀ (V : W.ProEtᵒᵖ) (b : S.target.obj.obj V) (i : Fin d),
      (θZ.inv ≫ Pi.π _ i).val.app ((proEtaleBaseChange q).op.obj V)
        ((proEtaleRingDirectImageMap q S.target S.source S.identification).hom.app V b) =
      (proEtaleRingDirectImageMap q R.target R.source R.identification).hom.app V
        ((θ.inv ≫ Pi.π _ i).val.app V b) := by
  exact ⟨transportedCoefficientBasis R S a d θ, basisCoordinate_unit R S a d θ⟩

end AlgebraicGeometry.Scheme.FiniteFreeDirectImage
