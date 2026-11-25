/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedExtensionZeroComparison
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenFlatResolution
import all WeilConjectures.AlgebraicGeometry.OrderedExchange.ProEtaleConstantReductionModels

/-! # Augmented strict reduction and ringed open extension

## References

* Stacks 00XZ, the datum's finite coefficient presheaf
* Stacks 03DA, 03DI
* Stacks 0E8I, 0GL1
* Stacks 03DJ
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance 2000] reductionModulesHasDerivedCategory
  reductionTowerHasDerivedCategory

/-- Reindex a ring sheaf from the open site's concrete category to the ambient slice. -/
def cbcSliceRing {T : Scheme.{u}} (W : T.ProEt)
    (S : Sheaf (ProEt.topology W.left) CommRingCat.{u + 1}) :=
  ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{u + 1}
    ((ProEt.topology T).over W) (ProEt.topology W.left)).obj S

private local instance sliceFunctor_cocontinuous (T : Scheme.{u}) (W : T.ProEt) :
    (cbcSliceFunctor T W).IsCocontinuous ((ProEt.topology T).over W)
      (ProEt.topology W.left) :=
  ( (ProEt.sliceEquiv T W).toAdjunction.isCocontinuous_iff_coverPreserving
    ((ProEt.topology T).over W) (ProEt.topology W.left)).mpr (ProEt.sliceFrom_cover T W)

private def finiteSliceIso {T : Scheme.{u}} (W : T.ProEt)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (reductionCoefficient T d n).over W ≅ cbcSliceRing W (reductionCoefficient W.left d n) :=
  (((Over.forget W).pushforwardContinuousSheafificationCompatibility CommRingCat.{u + 1}
    ((ProEt.topology T).over W) (ProEt.topology T)).app
      (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))).symm ≪≫
    ((cbcSliceFunctor T W).pushforwardContinuousSheafificationCompatibility
      CommRingCat.{u + 1} ((ProEt.topology T).over W) (ProEt.topology W.left)).app
        (AdicCoefficients.functionPresheaf W.left (A ⧸ d.ideal ^ (n + 1)))

private theorem finiteSliceIso_unit {T : Scheme.{u}} (W : T.ProEt)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) (V : Over W) :
    (toSheafify (ProEt.topology T)
      (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))).app (op V.left) ≫
        (finiteSliceIso W d n).hom.hom.app (op V) =
    (toSheafify (ProEt.topology W.left)
      (AdicCoefficients.functionPresheaf W.left (A ⧸ d.ideal ^ (n + 1)))).app
        (op ((cbcSliceFunctor T W).obj V)) := by
  have h₁ := (Over.forget W).toSheafify_pullbackSheafificationCompatibility
    CommRingCat.{u + 1} ((ProEt.topology T).over W) (ProEt.topology T)
    (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))
  have h₂ := (cbcSliceFunctor T W).toSheafify_pullbackSheafificationCompatibility
    CommRingCat.{u + 1} ((ProEt.topology T).over W) (ProEt.topology W.left)
    (AdicCoefficients.functionPresheaf W.left (A ⧸ d.ideal ^ (n + 1)))
  have h₁' := NatTrans.congr_app h₁ (op V)
  have h₂' := NatTrans.congr_app h₂ (op V)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₁' h₂'
  dsimp only [finiteSliceIso, Iso.trans_hom, Iso.symm_hom,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  have hid := congrArg (fun f ↦ f.hom.app (op V))
    (((Over.forget W).pushforwardContinuousSheafificationCompatibility
      CommRingCat.{u + 1} ((ProEt.topology T).over W) (ProEt.topology T)).app
        (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))).hom_inv_id
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app] at hid
  let α := ((Over.forget W).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{u + 1} ((ProEt.topology T).over W) (ProEt.topology T)).app
      (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))
  let β := ((cbcSliceFunctor T W).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{u + 1} ((ProEt.topology T).over W) (ProEt.topology W.left)).app
      (AdicCoefficients.functionPresheaf W.left (A ⧸ d.ideal ^ (n + 1)))
  calc
    _ = ((toSheafify ((ProEt.topology T).over W)
        ((Over.forget W).op ⋙
          AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))).app (op V) ≫
        α.hom.hom.app (op V)) ≫ α.inv.hom.app (op V) ≫ β.hom.hom.app (op V) :=
      congrArg (fun f ↦ f ≫ α.inv.hom.app (op V) ≫ β.hom.hom.app (op V)) h₁'.symm
    _ = _ := by
      simp only [Category.assoc] at hid ⊢
      rw [← Category.assoc (α.hom.hom.app _) (α.inv.hom.app _) _, hid,
        Category.id_comp]
      exact h₂'

attribute [local irreducible] finiteSliceIso

/-- The existing normalized finite slice map is invertible. -/
@[instance]
theorem cbcFiniteSliceMap_isIso {T : Scheme.{u}} (W : T.ProEt)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    IsIso (cbcFiniteSliceMap d T W n) := by
  have h : cbcFiniteSliceMap d T W n = (finiteSliceIso W d n).hom :=
    (cbcFiniteSliceMap_exists d T W n).unique
      (cbcFiniteSliceMap_exists d T W n).exists.choose_spec (finiteSliceIso_unit W d n)
  rw [h]
  infer_instance

/-- The existing finite restriction map, viewed as its canonical isomorphism. -/
def cbcFiniteRestriction {T : Scheme.{u}} (W : T.ProEt)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (reductionCoefficient T d n).over W ≅ cbcSliceRing W (reductionCoefficient W.left d n) :=
  asIso (cbcFiniteSliceMap d T W n)

private def finiteSliceSystemMap {T : Scheme.{u}} (W : T.ProEt)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    reductionCoefficientSystem T d ⋙ (ProEt.topology T).overPullback CommRingCat.{u + 1} W ⟶
      reductionCoefficientSystem W.left d ⋙
        (cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{u + 1}
          ((ProEt.topology T).over W) (ProEt.topology W.left) :=
  NatTrans.ofOpSequence (fun n ↦ (finiteSliceIso W d n).hom) (by
    intro n
    simp only [Functor.comp_map, reductionCoefficientSystem,
      AdicCoefficients.ringSystem, Functor.ofOpSequence_map_homOfLE_succ,
      finiteSliceIso, Iso.trans_hom, Iso.symm_hom]
    let α := (Over.forget W).pushforwardContinuousSheafificationCompatibility
      CommRingCat.{u + 1} ((ProEt.topology T).over W) (ProEt.topology T)
    let β := (cbcSliceFunctor T W).pushforwardContinuousSheafificationCompatibility
      CommRingCat.{u + 1} ((ProEt.topology T).over W) (ProEt.topology W.left)
    let f := AdicCoefficients.functionPresheafMap T
      (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
    let g := AdicCoefficients.functionPresheafMap W.left
      (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
    have ha := α.inv.naturality f
    have hb := β.hom.naturality g
    dsimp only [Functor.comp_map] at ha hb
    change _ ≫ (α.inv.app
        (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1))) ≫
        β.hom.app (AdicCoefficients.functionPresheaf W.left (A ⧸ d.ideal ^ (n + 1)))) =
      (α.inv.app (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1 + 1))) ≫
        β.hom.app (AdicCoefficients.functionPresheaf W.left
          (A ⧸ d.ideal ^ (n + 1 + 1)))) ≫ _
    let a₀ := α.inv.app
      (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))
    let a₁ := α.inv.app
      (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1 + 1)))
    let b₀ := β.hom.app
      (AdicCoefficients.functionPresheaf W.left (A ⧸ d.ideal ^ (n + 1)))
    let b₁ := β.hom.app
      (AdicCoefficients.functionPresheaf W.left (A ⧸ d.ideal ^ (n + 1 + 1)))
    let m := (presheafToSheaf ((ProEt.topology T).over W) CommRingCat.{u + 1}).map
      (Functor.whiskerLeft (Over.forget W).op f)
    have ha' : ((ProEt.topology T).overPullback CommRingCat.{u + 1} W).map
        (AdicCoefficients.coefficientMap T (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) ≫
        a₀ = a₁ ≫ m := ha
    have hb' : m ≫ b₀ = b₁ ≫
        ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{u + 1}
          ((ProEt.topology T).over W) (ProEt.topology W.left)).map
            (AdicCoefficients.coefficientMap W.left
              (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) := hb
    calc
      _ = (_ ≫ a₀) ≫ b₀ := (Category.assoc _ _ _).symm
      _ = (a₁ ≫ m) ≫ b₀ := congrArg (fun t ↦ t ≫ b₀) ha'
      _ = a₁ ≫ (m ≫ b₀) := Category.assoc _ _ _
      _ = a₁ ≫ (b₁ ≫ _) := congrArg (fun t ↦ a₁ ≫ t) hb'
      _ = _ := (Category.assoc _ _ _).symm)

private theorem finiteSliceMap_eq {T : Scheme.{u}} (W : T.ProEt)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    cbcFiniteSliceMap d T W n = (finiteSliceIso W d n).hom :=
  (cbcFiniteSliceMap_exists d T W n).unique
    (cbcFiniteSliceMap_exists d T W n).exists.choose_spec (finiteSliceIso_unit W d n)

private local instance overRing_limits {T : Scheme.{u}} (W : T.ProEt) :
    PreservesLimitsOfShape ℕᵒᵖ ((ProEt.topology T).overPullback CommRingCat.{u + 1} W) := by
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf ((ProEt.topology T).over W) CommRingCat.{u + 1})

private local instance sliceRing_limits {T : Scheme.{u}} (W : T.ProEt) :
    PreservesLimitsOfShape ℕᵒᵖ
      ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{u + 1}
        ((ProEt.topology T).over W) (ProEt.topology W.left)) := by
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf ((ProEt.topology T).over W) CommRingCat.{u + 1})

private def completedSliceIso {T : Scheme.{u}} (W : T.ProEt)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (completedReductionCoefficient T d).over W ≅
      cbcSliceRing W (completedReductionCoefficient W.left d) :=
  letI (n : ℕᵒᵖ) : IsIso ((finiteSliceSystemMap W d).app n) := by
    change IsIso (finiteSliceIso W d n.unop).hom
    infer_instance
  letI : IsIso (finiteSliceSystemMap W d) := NatIso.isIso_of_isIso_app _
  preservesLimitIso ((ProEt.topology T).overPullback CommRingCat.{u + 1} W)
      (reductionCoefficientSystem T d) ≪≫
    lim.mapIso (asIso (finiteSliceSystemMap W d)) ≪≫
    (preservesLimitIso ((cbcSliceFunctor T W).sheafPushforwardContinuous
      CommRingCat.{u + 1} ((ProEt.topology T).over W) (ProEt.topology W.left))
        (reductionCoefficientSystem W.left d)).symm

private theorem completedSliceIso_projection {T : Scheme.{u}} (W : T.ProEt)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (completedSliceIso W d).hom ≫
      ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{u + 1}
        ((ProEt.topology T).over W) (ProEt.topology W.left)).map
          (completedReductionProjection W.left d n) =
    ((ProEt.topology T).overPullback CommRingCat.{u + 1} W).map
        (completedReductionProjection T d n) ≫ cbcFiniteSliceMap d T W n := by
  simp only [completedSliceIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    completedReductionProjection, preservesLimitIso_inv_π, lim_map, limMap_π,
    Functor.mapIso_hom, asIso_hom, finiteSliceMap_eq]
  rw [← Category.assoc, preservesLimitIso_hom_π]
  rfl

/-- The existing completed slice map is invertible. -/
@[instance]
theorem cbcCompletedSliceMap_isIso {T : Scheme.{u}} (W : T.ProEt)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    IsIso (cbcCompletedSliceMap d T W) := by
  have h : cbcCompletedSliceMap d T W = (completedSliceIso W d).hom :=
    (cbcCompletedSliceMap_exists d T W).unique
      (cbcCompletedSliceMap_exists d T W).exists.choose_spec (completedSliceIso_projection W d)
  rw [h]
  infer_instance

/-- The existing completed restriction map, with its uniquely determined inverse. -/
def cbcCompletedRestriction {T : Scheme.{u}} (W : T.ProEt)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    (completedReductionCoefficient T d).over W ≅
      cbcSliceRing W (completedReductionCoefficient W.left d) :=
  asIso (cbcCompletedSliceMap d T W)

/-- Actual extension: transport along the concrete ringed slice equivalence, take the
extension presheaf, and sheafify as modules. -/
def cbcRingedOpenExtension {T : Scheme.{u}} (W : T.ProEt)
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology W.left) CommRingCat.{u + 1}}
    (c : R.over W ≅ cbcSliceRing W S) : reductionModules W.left S ⥤ reductionModules T R :=
  SheafOfModules.pushforward.{u + 1} (F := cbcSliceFunctor T W)
    ((sheafCompose ((ProEt.topology T).over W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom) ⋙
    SheafOfModules.localizedSystemExtension.{u + 1, u, u + 1} R W

open Classical in
/-- A section in the extension summand, followed by the module-sheafification unit. -/
def cbcOpenSection {T : Scheme.{u}} (W : T.ProEt)
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology W.left) CommRingCat.{u + 1}}
    (c : R.over W ≅ cbcSliceRing W S) (M : reductionModules W.left S)
    (V : T.ProEt) (a : V ⟶ W)
    (x : M.val.obj (op ((cbcSliceFunctor T W).obj (Over.mk a)))) :
    ((cbcRingedOpenExtension W c).obj M).val.obj (op V) :=
  ((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    (𝟙 (reductionModuleRing T R).obj)).unit.app
      ((SheafOfModules.extensionByZeroPresheaf (reductionModuleRing T R) W).obj
        ((SheafOfModules.pushforward.{u + 1} (F := cbcSliceFunctor T W)
          ((sheafCompose ((ProEt.topology T).over W)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)).obj M))).app (op V)
      (DirectSum.of _ a x)

private theorem openSection_hom_ext {T : Scheme.{u}} (W : T.ProEt)
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology W.left) CommRingCat.{u + 1}}
    (c : R.over W ≅ cbcSliceRing W S) (M : reductionModules W.left S)
    (N : reductionModules T R) (f g : (cbcRingedOpenExtension W c).obj M ⟶ N)
    (h : ∀ (V : T.ProEt) (a : V ⟶ W)
      (x : M.val.obj (op ((cbcSliceFunctor T W).obj (Over.mk a)))),
      f.val.app (op V) (cbcOpenSection W c M V a x) =
        g.val.app (op V) (cbcOpenSection W c M V a x)) : f = g := by
  classical
  apply (PresheafOfModules.sheafificationHomEquiv.{u + 1}
    (𝟙 (reductionModuleRing T R).obj)).injective
  ext V z
  induction z using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | of a x => exact h V.unop a x

private theorem openSection_map {T : Scheme.{u}} (W : T.ProEt)
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology W.left) CommRingCat.{u + 1}}
    (c : R.over W ≅ cbcSliceRing W S) {M N : reductionModules W.left S} (f : M ⟶ N)
    (V : T.ProEt) (a : V ⟶ W)
    (x : M.val.obj (op ((cbcSliceFunctor T W).obj (Over.mk a)))) :
    ((cbcRingedOpenExtension W c).map f).val.app (op V) (cbcOpenSection W c M V a x) =
      cbcOpenSection W c N V a (f.val.app _ x) := by
  classical
  let E := SheafOfModules.extensionByZeroPresheaf (reductionModuleRing T R) W
  let f' := (SheafOfModules.pushforward.{u + 1} (F := cbcSliceFunctor T W)
    (J := (ProEt.topology T).over W) (K := ProEt.topology W.left)
    (R := reductionModuleRing W.left S) (S := (reductionModuleRing T R).over W)
    ((sheafCompose ((ProEt.topology T).over W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)).map f
  have h := congrArg (fun t ↦ t.app (op V) (DirectSum.of _ a x))
    ((PresheafOfModules.sheafificationAdjunction.{u + 1}
      (𝟙 (reductionModuleRing T R).obj)).unit.naturality (E.map f'))
  change _ = _ at h
  dsimp only [Functor.comp_map, Functor.id_map, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at h
  symm at h
  change ((PresheafOfModules.sheafification.{u + 1} (𝟙 _)).map (E.map f')).val.app (op V)
      (cbcOpenSection W c M V a x) =
    ((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app (E.obj _)).app (op V)
      ((E.map f').app (op V) (DirectSum.of _ a x)) at h
  have hh : (E.map f').app (op V) (DirectSum.of _ a x) =
      DirectSum.of _ a (f.val.app _ x) := by
    exact DirectSum.lmap_of _ _ _
  rw [hh] at h
  exact h

private def sliceModuleEquivalence
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (e : C ≌ D) [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]
    (R : Sheaf J RingCat.{u + 1}) (S : Sheaf K RingCat.{u + 1})
    (c : S ≅ (e.inverse.sheafPushforwardContinuous RingCat.{u + 1} K J).obj R) :
    SheafOfModules.{u + 1} R ≌ SheafOfModules.{u + 1} S := by
  let ψ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{u + 1} J K).obj S :=
    { hom := Functor.whiskerRight e.op.unitIso.hom R.obj ≫
        Functor.whiskerLeft e.functor.op c.inv.hom }
  have H₁ : Functor.whiskerRight (NatTrans.op e.symm.counit) R.obj =
      ψ.hom ≫ e.functor.op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext U
    change R.obj.map _ =
      (R.obj.map _ ≫ c.inv.hom.app _) ≫ c.hom.hom.app _
    rw [Category.assoc]
    have hc := congrArg (fun f ↦ f.hom.app (e.functor.op.obj U)) c.inv_hom_id
    have hc' : c.inv.hom.app (e.functor.op.obj U) ≫
        c.hom.hom.app (e.functor.op.obj U) = 𝟙 _ := hc
    change R.obj.map (e.unitInv.app U.unop).op =
      R.obj.map (e.unitInv.app U.unop).op ≫
        (c.inv.hom.app (e.functor.op.obj U) ≫ c.hom.hom.app (e.functor.op.obj U))
    exact (Category.comp_id _).symm.trans
      (congrArg (fun f ↦ R.obj.map (e.unitInv.app U.unop).op ≫ f) hc'.symm)
  have H₂ : c.hom.hom ≫ e.inverse.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.symm.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext U
    change c.hom.hom.app U ≫
      (R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U))) ≫
        S.obj.map (e.counitInv.app U.unop).op = 𝟙 _
    rw [Category.assoc]
    have hn := c.inv.hom.naturality (e.counitInv.app U.unop).op
    change R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op ≫
      c.inv.hom.app U =
      c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U)) ≫
        S.obj.map (e.counitInv.app U.unop).op at hn
    rw [← hn]
    have hm : R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op = 𝟙 _ := by
      rw [← Functor.map_comp, ← op_comp]
      simp
    rw [← Category.assoc (R.obj.map _) (R.obj.map _) _, hm]
    change c.hom.hom.app U ≫ 𝟙 _ ≫ c.inv.hom.app U = 𝟙 _
    have hc : c.hom.hom.app U ≫ c.inv.hom.app U = 𝟙 _ :=
      congrArg (fun f ↦ f.hom.app U) c.hom_inv_id
    exact (congrArg (fun f ↦ c.hom.hom.app U ≫ f)
      (Category.id_comp (c.inv.hom.app U))).trans hc
  have : e.symm.functor.IsContinuous K J := inferInstanceAs (e.inverse.IsContinuous K J)
  have : e.symm.inverse.IsContinuous J K := inferInstanceAs (e.functor.IsContinuous J K)
  exact SheafOfModules.pushforwardPushforwardEquivalence e.symm c.hom ψ H₁ H₂

private def sliceModules {T : Scheme.{u}} (W : T.ProEt)
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology W.left) CommRingCat.{u + 1}}
    (c : R.over W ≅ cbcSliceRing W S) :
    reductionModules W.left S ≌ SheafOfModules.{u + 1} ((reductionModuleRing T R).over W) := by
  have : (ProEt.sliceEquiv T W).functor.IsCocontinuous
      ((ProEt.topology T).over W) (ProEt.topology W.left) :=
    sliceFunctor_cocontinuous T W
  have : (ProEt.sliceEquiv T W).symm.functor.IsContinuous
      (ProEt.topology W.left) ((ProEt.topology T).over W) :=
    (ProEt.sliceEquiv T W).toAdjunction.isContinuous_of_isCocontinuous
      ((ProEt.topology T).over W) (ProEt.topology W.left)
  have : (ProEt.sliceEquiv T W).symm.inverse.IsContinuous
      ((ProEt.topology T).over W) (ProEt.topology W.left) :=
    inferInstanceAs ((cbcSliceFunctor T W).IsContinuous
      ((ProEt.topology T).over W) (ProEt.topology W.left))
  exact sliceModuleEquivalence (ProEt.topology W.left) ((ProEt.topology T).over W)
    (ProEt.sliceEquiv T W).symm (reductionModuleRing W.left S)
    ((reductionModuleRing T R).over W)
    ((sheafCompose ((ProEt.topology T).over W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c)

private def openAdj {T : Scheme.{u}} (W : T.ProEt)
    {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology W.left) CommRingCat.{u + 1}}
    (c : R.over W ≅ cbcSliceRing W S) :
    cbcRingedOpenExtension W c ⊣
      SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1} R W ⋙
        (sliceModules W c).inverse :=
  (sliceModules W c).toAdjunction.comp
    (SheafOfModules.localizedSystemAdjunction.{u + 1, u, u + 1} R W)

section ScalarComparison
attribute [local irreducible] completedAdicChangeData completedReductionCoefficient

variable {T : Scheme.{u}} (W : T.ProEt)
  {R B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
  {S C : Sheaf (ProEt.topology W.left) CommRingCat.{u + 1}}
  (cR : R.over W ≅ cbcSliceRing W S) (cB : B.over W ≅ cbcSliceRing W C)
  (φ : R ⟶ B) (ψ : S ⟶ C)

/-- Compatibility of the two ringed restriction identifications with a coefficient map. -/
def CbcOpenRingSquare : Prop :=
  ((ProEt.topology T).overPullback CommRingCat.{u + 1} W).map φ ≫ cB.hom =
    cR.hom ≫ ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{u + 1}
      ((ProEt.topology T).over W) (ProEt.topology W.left)).map ψ

private abbrev openPresheaf
    {X : Scheme.{u}} (U : X.ProEt)
    {R' : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {S' : Sheaf (ProEt.topology U.left) CommRingCat.{u + 1}}
    (c : R'.over U ≅ cbcSliceRing U S') (M : reductionModules U.left S') :=
  (SheafOfModules.extensionByZeroPresheaf (reductionModuleRing X R') U).obj
    ((SheafOfModules.pushforward.{u + 1} (F := cbcSliceFunctor X U)
      ((sheafCompose ((ProEt.topology X).over U)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)).obj M)

private theorem raw_smul (h : CbcOpenRingSquare W cR cB φ ψ)
    (M : reductionModules W.left C) (V : T.ProEtᵒᵖ)
    (r : (reductionModuleRing T R).obj.obj V)
    (z : (openPresheaf W cR ((reductionRestrict W.left ψ).obj M)).obj V) :
    (((openPresheaf W cR ((reductionRestrict W.left ψ).obj M)).obj V).smul r).asHom.hom z =
    ((((PresheafOfModules.restrictScalars
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ).hom).obj
          (openPresheaf W cB M)).obj V).smul r).asHom.hom z := by
  let z' : DirectSum (V.unop ⟶ W) (fun a ↦
      M.val.obj (op ((cbcSliceFunctor T W).obj (Over.mk a)))) := z
  apply DFinsupp.ext
  intro a
  change (ψ.hom.app _ (cR.hom.hom.app (op (Over.mk a)) r)) • z' a =
    (cB.hom.hom.app (op (Over.mk a)) (φ.hom.app _ r)) • z' a
  have hh := congrArg (fun f : R.over W ⟶ cbcSliceRing W C ↦
      f.hom.app (op (Over.mk a)) r) h
  exact congrArg (fun s ↦ s • z' a) hh.symm

set_option backward.isDefEq.respectTransparency.types true in
private def rawIsoAt (h : CbcOpenRingSquare W cR cB φ ψ)
    (M : reductionModules W.left C) (V : T.ProEtᵒᵖ) :
    (openPresheaf W cR ((reductionRestrict W.left ψ).obj M)).obj V ≅
      ((PresheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ).hom).obj
            (openPresheaf W cB M)).obj V := by
  let P := openPresheaf W cR ((reductionRestrict W.left ψ).obj M)
  let Q := (PresheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ).hom).obj
        (openPresheaf W cB M)
  let e : (forget₂ _ AddCommGrpCat).obj (P.obj V) ≅
      (forget₂ _ AddCommGrpCat).obj (Q.obj V) := Iso.refl _
  refine ModuleCat.isoMk e ?_
  intro r
  apply AddCommGrpCat.ext
  intro z
  exact (raw_smul W cR cB φ ψ h M V r z).symm

set_option backward.isDefEq.respectTransparency.types true in
private theorem rawIsoAt_apply (h : CbcOpenRingSquare W cR cB φ ψ)
    (M : reductionModules W.left C) (V : T.ProEtᵒᵖ)
    (x : DirectSum (V.unop ⟶ W) (fun a ↦
      M.val.obj (op ((cbcSliceFunctor T W).obj (Over.mk a))))) :
    (rawIsoAt W cR cB φ ψ h M V).hom x = x := rfl

attribute [local irreducible] rawIsoAt

set_option backward.isDefEq.respectTransparency.types true in
private def openPresheafRestrictIso (h : CbcOpenRingSquare W cR cB φ ψ)
    (M : reductionModules W.left C) :
    openPresheaf W cR ((reductionRestrict W.left ψ).obj M) ≅
      (PresheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ).hom).obj
            (openPresheaf W cB M) := by
  refine PresheafOfModules.isoMk (rawIsoAt W cR cB φ ψ h M) ?_
  intro V V' f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h₁ := rawIsoAt_apply W cR cB φ ψ h M V'
    ((openPresheaf W cR ((reductionRestrict W.left ψ).obj M)).map f x)
  have h₂ := congrArg
    (((PresheafOfModules.restrictScalars
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ).hom).obj
          (openPresheaf W cB M)).map f)
    (rawIsoAt_apply W cR cB φ ψ h M V x)
  exact h₁.trans h₂.symm

set_option backward.isDefEq.respectTransparency.types true in
private theorem openPresheafRestrictIso_apply (h : CbcOpenRingSquare W cR cB φ ψ)
    (M : reductionModules W.left C) (V : T.ProEtᵒᵖ)
    (z : DirectSum (V.unop ⟶ W) (fun a ↦
      M.val.obj (op ((cbcSliceFunctor T W).obj (Over.mk a))))) :
    ((openPresheafRestrictIso W cR cB φ ψ h M).hom.app V) z = z :=
  rawIsoAt_apply W cR cB φ ψ h M V z

attribute [local irreducible] openPresheafRestrictIso

set_option backward.isDefEq.respectTransparency.types true in
private def openRestrictIsoApp (h : CbcOpenRingSquare W cR cB φ ψ)
    (M : reductionModules W.left C) :
    (cbcRingedOpenExtension W cR).obj ((reductionRestrict W.left ψ).obj M) ≅
      (reductionRestrict T φ).obj ((cbcRingedOpenExtension W cB).obj M) := by
  letI := CompletedTensorComparisonProof.restrictionSheafificationComparison_isIso
    ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ) (openPresheaf W cB M)
  exact (PresheafOfModules.sheafification.{u + 1} (𝟙 (reductionModuleRing T R).obj)).mapIso
    (openPresheafRestrictIso W cR cB φ ψ h M) ≪≫
  (asIso (CompletedTensorComparisonProof.restrictionSheafificationComparison
    ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ) (openPresheaf W cB M)))

set_option backward.isDefEq.respectTransparency.types true in
private theorem openRestrictIsoApp_section (h : CbcOpenRingSquare W cR cB φ ψ)
    (M : reductionModules W.left C) (V : T.ProEt) (a : V ⟶ W)
    (x : M.val.obj (op ((cbcSliceFunctor T W).obj (Over.mk a)))) :
    ((openRestrictIsoApp W cR cB φ ψ h M).hom).val.app (op V)
      (cbcOpenSection W cR ((reductionRestrict W.left ψ).obj M) V a x) =
        cbcOpenSection W cB M V a x := by
  classical
  let α := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ
  let P := openPresheaf W cR ((reductionRestrict W.left ψ).obj M)
  let Q := openPresheaf W cB M
  let e := openPresheafRestrictIso W cR cB φ ψ h M
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 (reductionModuleRing T R).obj)
  let cmp := CompletedTensorComparisonProof.restrictionSheafificationComparison α Q
  have hn := congrArg (fun f : P ⟶
      (SheafOfModules.forget _).obj
        ((PresheafOfModules.sheafification.{u + 1} (𝟙 (reductionModuleRing T R).obj)).obj
          ((PresheafOfModules.restrictScalars α.hom).obj Q)) ↦
        f.app (op V) (DirectSum.of _ a x)) (adj.unit.naturality e.hom)
  have hc := (PresheafOfModules.sheafificationHomEquiv
    (P := (PresheafOfModules.restrictScalars α.hom).obj Q)
    (F := (SheafOfModules.restrictScalars α).obj
      ((PresheafOfModules.sheafification.{u + 1} (𝟙 (reductionModuleRing T B).obj)).obj Q))
    (𝟙 (reductionModuleRing T R).obj)).apply_symm_apply
      ((PresheafOfModules.restrictScalars α.hom).map
        ((PresheafOfModules.sheafificationAdjunction.{u + 1}
          (𝟙 (reductionModuleRing T B).obj)).unit.app Q))
  have hc' := congrArg (fun f ↦ f.app (op V) (DirectSum.of _ a x)) hc
  have he := openPresheafRestrictIso_apply W cR cB φ ψ h M (op V)
    (DirectSum.of _ a x)
  change (adj.unit.app _).app (op V) (e.hom.app (op V) (DirectSum.of _ a x)) =
    ((PresheafOfModules.sheafification.{u + 1} (𝟙 (reductionModuleRing T R).obj)).map
      e.hom).val.app (op V) ((adj.unit.app P).app (op V) (DirectSum.of _ a x)) at hn
  change cmp.val.app (op V) ((adj.unit.app _).app (op V) (DirectSum.of _ a x)) =
    cbcOpenSection W cB M V a x at hc'
  change cmp.val.app (op V)
    (((PresheafOfModules.sheafification.{u + 1} (𝟙 (reductionModuleRing T R).obj)).map
      e.hom).val.app (op V) ((adj.unit.app P).app (op V) (DirectSum.of _ a x))) = _
  exact (congrArg (cmp.val.app (op V)) hn.symm).trans
    ((congrArg (fun z ↦ cmp.val.app (op V) ((adj.unit.app _).app (op V) z)) he).trans hc')

attribute [local irreducible] openRestrictIsoApp

set_option backward.isDefEq.respectTransparency.types true in
/-- Extension commutes with scalar restriction by the identity on extension summands. -/
theorem cbcOpenRestrictIso_existsUnique (_h : CbcOpenRingSquare W cR cB φ ψ) :
    ∃! θ : reductionRestrict W.left ψ ⋙ cbcRingedOpenExtension W cR ≅
        cbcRingedOpenExtension W cB ⋙ reductionRestrict T φ,
      ∀ (M : reductionModules W.left C) (V : T.ProEt) (a : V ⟶ W)
        (x : M.val.obj (op ((cbcSliceFunctor T W).obj (Over.mk a)))),
        (θ.hom.app M).val.app (op V)
          (cbcOpenSection W cR ((reductionRestrict W.left ψ).obj M) V a x) =
        cbcOpenSection W cB M V a x := by
  let e := openRestrictIsoApp W cR cB φ ψ _h
  have hn {M N : reductionModules W.left C} (f : M ⟶ N) :
      (cbcRingedOpenExtension W cR).map ((reductionRestrict W.left ψ).map f) ≫
        (e N).hom =
      (e M).hom ≫ (reductionRestrict T φ).map ((cbcRingedOpenExtension W cB).map f) := by
    apply openSection_hom_ext W cR
    intro V a x
    change (e N).hom.val.app (op V)
      (((cbcRingedOpenExtension W cR).map ((reductionRestrict W.left ψ).map f)).val.app
        (op V) (cbcOpenSection W cR _ V a x)) =
      ((cbcRingedOpenExtension W cB).map f).val.app (op V)
        ((e M).hom.val.app (op V) (cbcOpenSection W cR _ V a x))
    have hmap := openSection_map W cR ((reductionRestrict W.left ψ).map f) V a x
    have hN := openRestrictIsoApp_section W cR cB φ ψ _h N V a
      (f.val.app (op ((cbcSliceFunctor T W).obj (Over.mk a))) x)
    have hM := openRestrictIsoApp_section W cR cB φ ψ _h M V a x
    have hmap' := openSection_map W cB f V a x
    exact (congrArg ((e N).hom.val.app (op V)) hmap).trans
      (hN.trans (hmap'.symm.trans
        (congrArg (((cbcRingedOpenExtension W cB).map f).val.app (op V)) hM.symm)))
  refine ⟨NatIso.ofComponents e (fun f ↦ hn f), ?_, ?_⟩
  · exact openRestrictIsoApp_section W cR cB φ ψ _h
  · intro θ hθ
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply openSection_hom_ext W cR
    intro V a x
    exact (hθ M V a x).trans (openRestrictIsoApp_section W cR cB φ ψ _h M V a x).symm

/-- Scalar restriction comparison with the prescribed underlying summand maps. -/
def cbcOpenRestrictIso (h : CbcOpenRingSquare W cR cB φ ψ) :=
  (cbcOpenRestrictIso_existsUnique W cR cB φ ψ h).exists.choose
private theorem openSection_smul (M : reductionModules W.left S)
    (V : T.ProEt) (a : V ⟶ W) (r : R.obj.obj (op V))
    (x : M.val.obj (op ((cbcSliceFunctor T W).obj (Over.mk a)))) :
    r • cbcOpenSection W cR M V a x =
      cbcOpenSection W cR M V a (cR.hom.hom.app (op (Over.mk a)) r • x) := by
  classical
  unfold cbcOpenSection
  let E := (SheafOfModules.extensionByZeroPresheaf (reductionModuleRing T R) W).obj
    ((SheafOfModules.pushforward.{u + 1} (F := cbcSliceFunctor T W)
      ((sheafCompose ((ProEt.topology T).over W)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map cR.hom)).obj M)
  let η := ((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 (reductionModuleRing T R).obj)).unit.app E).app (op V)
  change r • η (DirectSum.of _ a x) =
    η (DirectSum.of _ a (cR.hom.hom.app (op (Over.mk a)) r • x))
  have hh := η.hom.map_smul r (DirectSum.of _ a x)
  exact hh.symm.trans (congrArg η ((DirectSum.of_smul _ _ _ _).symm))

private def scalarHom (h : CbcOpenRingSquare W cR cB φ ψ)
    (M : reductionModules W.left S) :
    (reductionChange T φ).obj ((cbcRingedOpenExtension W cR).obj M) ⟶
      (cbcRingedOpenExtension W cB).obj ((reductionChange W.left ψ).obj M) :=
  ((ordinaryAdjunction_exists T φ).choose.homEquiv _ _).symm
    ((cbcRingedOpenExtension W cR).map (reductionUnit W.left ψ M) ≫
      (cbcOpenRestrictIso W cR cB φ ψ h).hom.app ((reductionChange W.left ψ).obj M))

private theorem scalarHom_unit (h : CbcOpenRingSquare W cR cB φ ψ)
    (M : reductionModules W.left S) (V : T.ProEt) (a : V ⟶ W)
    (x : M.val.obj (op ((cbcSliceFunctor T W).obj (Over.mk a)))) :
    (scalarHom W cR cB φ ψ h M).val.app (op V)
      (reductionTensorSection T φ ((cbcRingedOpenExtension W cR).obj M) (op V) 1
        (cbcOpenSection W cR M V a x)) =
      cbcOpenSection W cB ((reductionChange W.left ψ).obj M) V a
        (reductionTensorSection W.left ψ M
          (op ((cbcSliceFunctor T W).obj (Over.mk a))) 1 x) := by
  have hu := eq_of_heq ((ordinaryAdjunction_exists T φ).choose_spec
    ((cbcRingedOpenExtension W cR).obj M)
    ((cbcRingedOpenExtension W cB).obj ((reductionChange W.left ψ).obj M))
    (scalarHom W cR cB φ ψ h M) (op V) (cbcOpenSection W cR M V a x))
  have he := ((ordinaryAdjunction_exists T φ).choose.homEquiv _ _).apply_symm_apply
    ((cbcRingedOpenExtension W cR).map (reductionUnit W.left ψ M) ≫
      (cbcOpenRestrictIso W cR cB φ ψ h).hom.app ((reductionChange W.left ψ).obj M))
  have he' := congrArg (fun f ↦ f.val.app (op V) (cbcOpenSection W cR M V a x)) he
  exact hu.symm.trans (he'.trans (by
    change ((cbcOpenRestrictIso W cR cB φ ψ h).hom.app _).val.app (op V)
      (((cbcRingedOpenExtension W cR).map (reductionUnit W.left ψ M)).val.app (op V)
        (cbcOpenSection W cR M V a x)) = _
    rw [openSection_map]
    erw [(cbcOpenRestrictIso_existsUnique W cR cB φ ψ h).exists.choose_spec]
    rw [reductionUnit_apply]))

private theorem scalarHom_tensor (h : CbcOpenRingSquare W cR cB φ ψ)
    (M : reductionModules W.left S) (V : T.ProEt) (a : V ⟶ W)
    (b : B.obj.obj (op V))
    (x : M.val.obj (op ((cbcSliceFunctor T W).obj (Over.mk a)))) :
    (scalarHom W cR cB φ ψ h M).val.app (op V)
      (reductionTensorSection T φ ((cbcRingedOpenExtension W cR).obj M) (op V) b
        (cbcOpenSection W cR M V a x)) =
      cbcOpenSection W cB ((reductionChange W.left ψ).obj M) V a
        (reductionTensorSection W.left ψ M
          (op ((cbcSliceFunctor T W).obj (Over.mk a)))
          (cB.hom.hom.app (op (Over.mk a)) b) x) := by
  have hb := tensorSection_smul T φ ((cbcRingedOpenExtension W cR).obj M)
    (op V) b 1 (cbcOpenSection W cR M V a x)
  rw [mul_one] at hb
  rw [← hb, map_smul, scalarHom_unit, openSection_smul]
  congr 1
  have ht := tensorSection_smul W.left ψ M
    (op ((cbcSliceFunctor T W).obj (Over.mk a)))
    (cB.hom.hom.app (op (Over.mk a)) b) 1 x
  simpa only [mul_one] using ht

private abbrev openStar
    {R' : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    {S' : Sheaf (ProEt.topology W.left) CommRingCat.{u + 1}}
    (c : R'.over W ≅ cbcSliceRing W S') :=
  SheafOfModules.localizedSystemRestriction.{u + 1, u, u + 1} R' W ⋙
    (sliceModules W c).inverse

private def rightSquareAt
    (h : ((ProEt.topology T).overPullback CommRingCat.{u + 1} W).map φ ≫ cB.hom =
      cR.hom ≫ ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{u + 1}
        ((ProEt.topology T).over W) (ProEt.topology W.left)).map ψ)
    (N : reductionModules T B) (U : W.left.ProEtᵒᵖ) :
    ((openStar W cR).obj ((reductionRestrict T φ).obj N)).val.obj U ≅
      ((reductionRestrict W.left ψ).obj ((openStar W cB).obj N)).val.obj U := by
  let P := ((openStar W cR).obj ((reductionRestrict T φ).obj N)).val.obj U
  let Q := ((reductionRestrict W.left ψ).obj ((openStar W cB).obj N)).val.obj U
  let e : (forget₂ _ AddCommGrpCat).obj P ≅ (forget₂ _ AddCommGrpCat).obj Q := Iso.refl _
  refine ModuleCat.isoMk e ?_
  intro s
  apply AddCommGrpCat.ext
  intro x
  let V := (ProEt.sliceEquiv T W).inverse.obj U.unop
  have hi : cR.inv ≫ ((ProEt.topology T).overPullback CommRingCat.{u + 1} W).map φ =
      ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{u + 1}
        ((ProEt.topology T).over W) (ProEt.topology W.left)).map ψ ≫ cB.inv := by
    apply (cancel_mono cB.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h, ← Category.assoc, cR.inv_hom_id, Category.id_comp]
  have hh := congrArg (fun f ↦ f.hom.app (op V)
    (S.obj.map ((ProEt.sliceEquiv T W).counit.app U.unop).op s)) hi
  have hn := congrArg (fun f ↦ f s)
    (ψ.hom.naturality ((ProEt.sliceEquiv T W).counit.app U.unop).op)
  change φ.hom.app (op V.left)
      (cR.inv.hom.app (op V)
        (S.obj.map ((ProEt.sliceEquiv T W).counit.app U.unop).op s)) =
    cB.inv.hom.app (op V)
      (ψ.hom.app (op ((cbcSliceFunctor T W).obj V))
        (S.obj.map ((ProEt.sliceEquiv T W).counit.app U.unop).op s)) at hh
  change _ = _ at hn
  let x' : N.val.obj (op V.left) := x
  change cB.inv.hom.app (op V)
      (C.obj.map ((ProEt.sliceEquiv T W).counit.app U.unop).op (ψ.hom.app U s)) • x' =
    φ.hom.app (op V.left)
      (cR.inv.hom.app (op V)
        (S.obj.map ((ProEt.sliceEquiv T W).counit.app U.unop).op s)) • x'
  exact congrArg (fun r ↦ r • x') ((congrArg (cB.inv.hom.app (op V)) hn.symm).trans hh.symm)

private theorem rightSquareAt_apply
    (h : ((ProEt.topology T).overPullback CommRingCat.{u + 1} W).map φ ≫ cB.hom =
      cR.hom ≫ ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{u + 1}
        ((ProEt.topology T).over W) (ProEt.topology W.left)).map ψ)
    (N : reductionModules T B) (U : W.left.ProEtᵒᵖ)
    (x : ((openStar W cR).obj ((reductionRestrict T φ).obj N)).val.obj U) :
    (rightSquareAt W cR cB φ ψ h N U).hom x = x := rfl

private theorem rightSquareAt_inv_apply
    (h : ((ProEt.topology T).overPullback CommRingCat.{u + 1} W).map φ ≫ cB.hom =
      cR.hom ≫ ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{u + 1}
        ((ProEt.topology T).over W) (ProEt.topology W.left)).map ψ)
    (N : reductionModules T B) (U : W.left.ProEtᵒᵖ)
    (x : ((reductionRestrict W.left ψ).obj ((openStar W cB).obj N)).val.obj U) :
    (rightSquareAt W cR cB φ ψ h N U).inv x = x := by
  have hh := rightSquareAt_apply W cR cB φ ψ h N U
    ((rightSquareAt W cR cB φ ψ h N U).inv x)
  have hi := congrArg (fun f ↦ f x) (rightSquareAt W cR cB φ ψ h N U).inv_hom_id
  exact hh.symm.trans hi

attribute [local irreducible] rightSquareAt

private def rightSquareObj
    (h : ((ProEt.topology T).overPullback CommRingCat.{u + 1} W).map φ ≫ cB.hom =
      cR.hom ≫ ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{u + 1}
        ((ProEt.topology T).over W) (ProEt.topology W.left)).map ψ)
    (N : reductionModules T B) :
    (openStar W cR).obj ((reductionRestrict T φ).obj N) ≅
      (reductionRestrict W.left ψ).obj ((openStar W cB).obj N) := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (rightSquareAt W cR cB φ ψ h N) ?_
  intro U V f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h₁ := rightSquareAt_apply W cR cB φ ψ h N V
    (((openStar W cR).obj ((reductionRestrict T φ).obj N)).val.map f x)
  have h₂ := congrArg
    (((reductionRestrict W.left ψ).obj ((openStar W cB).obj N)).val.map f)
    (rightSquareAt_apply W cR cB φ ψ h N U x)
  exact h₁.trans h₂.symm

private def rightSquare
    (h : ((ProEt.topology T).overPullback CommRingCat.{u + 1} W).map φ ≫ cB.hom =
      cR.hom ≫ ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{u + 1}
        ((ProEt.topology T).over W) (ProEt.topology W.left)).map ψ) :
    reductionRestrict T φ ⋙ openStar W cR ≅
      openStar W cB ⋙ reductionRestrict W.left ψ := by
  refine NatIso.ofComponents (rightSquareObj W cR cB φ ψ h) ?_
  intro M N f
  ext U x
  exact (rightSquareAt_apply W cR cB φ ψ h N U (f.val.app _ x)).trans
    (congrArg (f.val.app _) (rightSquareAt_apply W cR cB φ ψ h M U x)).symm

private def scalarIso
    (h : ((ProEt.topology T).overPullback CommRingCat.{u + 1} W).map φ ≫ cB.hom =
      cR.hom ≫ ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{u + 1}
        ((ProEt.topology T).over W) (ProEt.topology W.left)).map ψ) :
    cbcRingedOpenExtension W cR ⋙ reductionChange T φ ≅
      reductionChange W.left ψ ⋙ cbcRingedOpenExtension W cB :=
  Adjunction.leftAdjointUniq
    ((openAdj W cR).comp (ordinaryAdjunction_exists T φ).choose)
    (((ordinaryAdjunction_exists W.left ψ).choose.comp (openAdj W cB)).ofNatIsoRight
      (rightSquare W cR cB φ ψ h).symm)

private theorem openAdj_apply
    (M : reductionModules W.left S) (N : reductionModules T R)
    (f : (cbcRingedOpenExtension W cR).obj M ⟶ N)
    (U : W.left.ProEtᵒᵖ) (x : M.val.obj U) :
    ((openAdj W cR).homEquiv M N f).val.app U x =
      f.val.app (op ((ProEt.sliceFrom T W).obj U.unop).left)
        (cbcOpenSection W cR M ((ProEt.sliceFrom T W).obj U.unop).left
          ((ProEt.sliceFrom T W).obj U.unop).hom
          (M.val.map ((ProEt.sliceEquiv T W).counit.app U.unop).op x)) := by
  rw [Adjunction.homEquiv_unit]
  have hu := (SheafOfModules.localizedSystemAdjunction_existsUnique.{u + 1, u, u + 1}
    R W).exists.choose_spec ((sliceModules W cR).functor.obj M)
    (op ((ProEt.sliceFrom T W).obj U.unop))
    (M.val.map ((ProEt.sliceEquiv T W).counit.app U.unop).op x)
  have hs : ((openAdj W cR).unit.app M).val.app U x =
      cbcOpenSection W cR M ((ProEt.sliceFrom T W).obj U.unop).left
        ((ProEt.sliceFrom T W).obj U.unop).hom
        (M.val.map ((ProEt.sliceEquiv T W).counit.app U.unop).op x) := by
    change ((SheafOfModules.localizedSystemAdjunction.{u + 1, u, u + 1} R W).unit.app
      ((sliceModules W cR).functor.obj M)).val.app
        (op ((ProEt.sliceFrom T W).obj U.unop))
        (M.val.map ((ProEt.sliceEquiv T W).counit.app U.unop).op x) = _
    exact hu
  exact congrArg (f.val.app _) hs

private theorem scalarHom_eq_iso (h : CbcOpenRingSquare W cR cB φ ψ)
    (M : reductionModules W.left S) :
    scalarHom W cR cB φ ψ h M = (scalarIso W cR cB φ ψ h).hom.app M := by
  let aT := (ordinaryAdjunction_exists T φ).choose
  let aW := (ordinaryAdjunction_exists W.left ψ).choose
  let A := (openAdj W cR).comp aT
  let B := (aW.comp (openAdj W cB)).ofNatIsoRight (rightSquare W cR cB φ ψ h).symm
  apply (A.homEquiv _ _).injective
  change A.homEquiv _ _ (scalarHom W cR cB φ ψ h M) =
    A.homEquiv _ _ ((Adjunction.leftAdjointUniq A B).hom.app M)
  refine Eq.trans ?_ (Adjunction.homEquiv_leftAdjointUniq_hom_app A B M).symm
  change (openAdj W cR).homEquiv _ _ (aT.homEquiv _ _
    (scalarHom W cR cB φ ψ h M)) = B.unit.app M
  ext U x
  rw [openAdj_apply]
  have hu := eq_of_heq ((ordinaryAdjunction_exists T φ).choose_spec
    ((cbcRingedOpenExtension W cR).obj M)
    ((cbcRingedOpenExtension W cB).obj ((reductionChange W.left ψ).obj M))
    (scalarHom W cR cB φ ψ h M)
    (op ((ProEt.sliceFrom T W).obj U.unop).left)
    (cbcOpenSection W cR M ((ProEt.sliceFrom T W).obj U.unop).left
      ((ProEt.sliceFrom T W).obj U.unop).hom
      (M.val.map ((ProEt.sliceEquiv T W).counit.app U.unop).op x)))
  refine hu.trans ((scalarHom_unit W cR cB φ ψ h M
    ((ProEt.sliceFrom T W).obj U.unop).left
    ((ProEt.sliceFrom T W).obj U.unop).hom
    (M.val.map ((ProEt.sliceEquiv T W).counit.app U.unop).op x)).trans ?_)
  have hr : ((rightSquare W cR cB φ ψ h).inv.app
      ((cbcRingedOpenExtension W cB).obj ((reductionChange W.left ψ).obj M))).val.app U
      (((aW.comp (openAdj W cB)).unit.app M).val.app U x) =
      ((aW.comp (openAdj W cB)).unit.app M).val.app U x :=
    rightSquareAt_inv_apply W cR cB φ ψ h _ U _
  change _ = ((rightSquare W cR cB φ ψ h).inv.app _).val.app U
    (((aW.comp (openAdj W cB)).unit.app M).val.app U x)
  refine Eq.trans ?_ hr.symm
  have hb : (aW.comp (openAdj W cB)).unit.app M =
      aW.unit.app M ≫ (reductionRestrict W.left ψ).map
        ((openAdj W cB).unit.app ((reductionChange W.left ψ).obj M)) :=
    Adjunction.comp_unit_app _ _ M
  rw [hb]
  have hw := reductionUnit_apply W.left ψ M U x
  have hj := openAdj_apply W cB ((reductionChange W.left ψ).obj M)
    ((cbcRingedOpenExtension W cB).obj ((reductionChange W.left ψ).obj M))
    (𝟙 _) U (reductionTensorSection W.left ψ M U 1 x)
  have hi : (openAdj W cB).homEquiv _ _ (𝟙 _) =
      (openAdj W cB).unit.app ((reductionChange W.left ψ).obj M) := by
    rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have hj' := (congrArg (fun f ↦ f.val.app U
    (reductionTensorSection W.left ψ M U 1 x)) hi).symm.trans hj
  change _ = ((openAdj W cB).unit.app _).val.app U ((aW.unit.app M).val.app U x)
  change _ = ((openAdj W cB).unit.app _).val.app U ((reductionUnit W.left ψ M).val.app U x)
  rw [hw]
  refine Eq.trans ?_ hj'.symm
  have hn := PresheafOfModules.naturality_apply (reductionUnit W.left ψ M).val
    ((ProEt.sliceEquiv T W).counit.app U.unop).op x
  rw [reductionUnit_apply, reductionUnit_apply] at hn
  exact congrArg (cbcOpenSection W cB ((reductionChange W.left ψ).obj M)
    ((ProEt.sliceFrom T W).obj U.unop).left ((ProEt.sliceFrom T W).obj U.unop).hom) hn

private theorem scalarUnique (h : CbcOpenRingSquare W cR cB φ ψ)
    (β : cbcRingedOpenExtension W cR ⋙ reductionChange T φ ≅
        reductionChange W.left ψ ⋙ cbcRingedOpenExtension W cB)
    (hβ : ∀ (M : reductionModules W.left S) (V : T.ProEt) (a : V ⟶ W)
        (b : B.obj.obj (op V))
        (x : M.val.obj (op ((cbcSliceFunctor T W).obj (Over.mk a)))),
        (β.hom.app M).val.app (op V)
          (reductionTensorSection T φ ((cbcRingedOpenExtension W cR).obj M) (op V) b
            (cbcOpenSection W cR M V a x)) =
        cbcOpenSection W cB ((reductionChange W.left ψ).obj M) V a
          (reductionTensorSection W.left ψ M
            (op ((cbcSliceFunctor T W).obj (Over.mk a)))
            (cB.hom.hom.app (op (Over.mk a)) b) x)) :
    β = scalarIso W cR cB φ ψ h := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  rw [← scalarHom_eq_iso]
  apply ((ordinaryAdjunction_exists T φ).choose.homEquiv _ _).injective
  apply openSection_hom_ext W cR
  intro V a x
  have h₁ := eq_of_heq ((ordinaryAdjunction_exists T φ).choose_spec _ _
    (β.hom.app M) (op V) (cbcOpenSection W cR M V a x))
  have h₂ := eq_of_heq ((ordinaryAdjunction_exists T φ).choose_spec _ _
    (scalarHom W cR cB φ ψ h M) (op V) (cbcOpenSection W cR M V a x))
  refine h₁.trans (Eq.trans ?_ h₂.symm)
  have hb := hβ M V a 1 x
  have hu := scalarHom_unit W cR cB φ ψ h M V a x
  rw [map_one] at hb
  exact hb.trans hu.symm

/-- The scalar-extension comparison is uniquely fixed before restricting coefficients. -/
theorem cbcOpenScalarIso_existsUnique
    (_h : CbcOpenRingSquare W cR cB φ ψ) :
    ∃! β : cbcRingedOpenExtension W cR ⋙ reductionChange T φ ≅
        reductionChange W.left ψ ⋙ cbcRingedOpenExtension W cB,
      ∀ (M : reductionModules W.left S) (V : T.ProEt) (a : V ⟶ W)
        (b : B.obj.obj (op V))
        (x : M.val.obj (op ((cbcSliceFunctor T W).obj (Over.mk a)))),
        (β.hom.app M).val.app (op V)
          (reductionTensorSection T φ ((cbcRingedOpenExtension W cR).obj M) (op V) b
            (cbcOpenSection W cR M V a x)) =
        cbcOpenSection W cB ((reductionChange W.left ψ).obj M) V a
          (reductionTensorSection W.left ψ M
            (op ((cbcSliceFunctor T W).obj (Over.mk a)))
            (cB.hom.hom.app (op (Over.mk a)) b) x) := by
  refine ⟨scalarIso W cR cB φ ψ _h, ?_, ?_⟩
  · intro M V a b x
    rw [← scalarHom_eq_iso]
    exact scalarHom_tensor W cR cB φ ψ _h M V a b x
  · intro β hβ
    exact scalarUnique W cR cB φ ψ _h β hβ

/-- The canonical coefficient-linear comparison, with its pure tensor normalization. -/
def cbcOpenScalarIso (h : CbcOpenRingSquare W cR cB φ ψ) :=
  (cbcOpenScalarIso_existsUnique W cR cB φ ψ h).exists.choose

private def openDelta (h : CbcOpenRingSquare W cR cB φ ψ) :
    cbcRingedOpenExtension W cR ⋙ reductionChange T φ ⋙ reductionRestrict T φ ≅
      reductionChange W.left ψ ⋙ reductionRestrict W.left ψ ⋙ cbcRingedOpenExtension W cR :=
  Functor.isoWhiskerRight (cbcOpenScalarIso W cR cB φ ψ h) (reductionRestrict T φ) ≪≫
    Functor.isoWhiskerLeft (reductionChange W.left ψ)
      (cbcOpenRestrictIso W cR cB φ ψ h).symm

private theorem openDelta_hom (h : CbcOpenRingSquare W cR cB φ ψ)
    (M : reductionModules W.left S) (V : T.ProEt) (a : V ⟶ W)
    (b : B.obj.obj (op V))
    (x : M.val.obj (op ((cbcSliceFunctor T W).obj (Over.mk a)))) :
    ((openDelta W cR cB φ ψ h).hom.app M).val.app (op V)
      (reductionTensorSection T φ ((cbcRingedOpenExtension W cR).obj M) (op V) b
        (cbcOpenSection W cR M V a x)) =
      cbcOpenSection W cR ((reductionRestrict W.left ψ).obj
        ((reductionChange W.left ψ).obj M)) V a
        (reductionTensorSection W.left ψ M
          (op ((cbcSliceFunctor T W).obj (Over.mk a)))
          (cB.hom.hom.app (op (Over.mk a)) b) x) := by
  let N := (reductionChange W.left ψ).obj M
  let θ := cbcOpenRestrictIso W cR cB φ ψ h
  have hθ := (cbcOpenRestrictIso_existsUnique W cR cB φ ψ h).exists.choose_spec N V a
    (reductionTensorSection W.left ψ M
      (op ((cbcSliceFunctor T W).obj (Over.mk a)))
      (cB.hom.hom.app (op (Over.mk a)) b) x)
  have hi := congrArg (fun f ↦ f.val.app (op V)
    (cbcOpenSection W cR ((reductionRestrict W.left ψ).obj N) V a
      (reductionTensorSection W.left ψ M
        (op ((cbcSliceFunctor T W).obj (Over.mk a)))
        (cB.hom.hom.app (op (Over.mk a)) b) x))) (θ.app N).hom_inv_id
  change _ = _ at hi
  change (θ.inv.app N).val.app (op V)
    (((cbcOpenScalarIso W cR cB φ ψ h).hom.app M).val.app (op V)
      (reductionTensorSection T φ ((cbcRingedOpenExtension W cR).obj M) (op V) b
        (cbcOpenSection W cR M V a x))) = _
  erw [(cbcOpenScalarIso_existsUnique W cR cB φ ψ h).exists.choose_spec]
  exact (congrArg ((θ.inv.app N).val.app (op V)) hθ.symm).trans hi

private theorem openDelta_inv (h : CbcOpenRingSquare W cR cB φ ψ)
    (M : reductionModules W.left S) (V : T.ProEt) (a : V ⟶ W)
    (s : C.obj.obj (op ((cbcSliceFunctor T W).obj (Over.mk a))))
    (x : M.val.obj (op ((cbcSliceFunctor T W).obj (Over.mk a)))) :
    ((openDelta W cR cB φ ψ h).inv.app M).val.app (op V)
      (cbcOpenSection W cR ((reductionRestrict W.left ψ).obj
        ((reductionChange W.left ψ).obj M)) V a
        (reductionTensorSection W.left ψ M
          (op ((cbcSliceFunctor T W).obj (Over.mk a))) s x)) =
      reductionTensorSection T φ ((cbcRingedOpenExtension W cR).obj M) (op V)
        (cB.inv.hom.app (op (Over.mk a)) s) (cbcOpenSection W cR M V a x) := by
  let δ := openDelta W cR cB φ ψ h
  let b := cB.inv.hom.app (op (Over.mk a)) s
  have hh := openDelta_hom W cR cB φ ψ h M V a b x
  have hb : cB.hom.hom.app (op (Over.mk a)) b = s :=
    congrArg (fun f ↦ f.hom.app (op (Over.mk a)) s) cB.inv_hom_id
  rw [hb] at hh
  have hi := congrArg (fun f ↦ f.val.app (op V)
    (reductionTensorSection T φ ((cbcRingedOpenExtension W cR).obj M) (op V) b
      (cbcOpenSection W cR M V a x))) (δ.app M).hom_inv_id
  exact (congrArg ((δ.inv.app M).val.app (op V)) hh).symm.trans hi

attribute [local irreducible] openDelta

private theorem tensorSection_restrict (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : reductionModules X R) {U V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (s : S.obj.obj U) (x : M.val.obj U) :
    ((reductionChange X φ).obj M).val.map f (reductionTensorSection X φ M U s x) =
      reductionTensorSection X φ M V (S.obj.map f s) (M.val.map f x) := by
  have hs := tensorSection_smul X φ M U s 1 x
  have ht := tensorSection_smul X φ M V (S.obj.map f s) 1 (M.val.map f x)
  rw [mul_one] at hs ht
  have hu := PresheafOfModules.naturality_apply (reductionUnit X φ M).val f x
  rw [reductionUnit_apply, reductionUnit_apply] at hu
  calc
    _ = ((reductionChange X φ).obj M).val.map f
        (s • reductionTensorSection X φ M U 1 x) :=
      congrArg (((reductionChange X φ).obj M).val.map f) hs.symm
    _ = S.obj.map f s •
        (show ((reductionChange X φ).obj M).val.obj V from
          ((reductionChange X φ).obj M).val.map f
            (reductionTensorSection X φ M U 1 x)) :=
      ((reductionChange X φ).obj M).val.map_smul f s _
    _ = S.obj.map f s • reductionTensorSection X φ M V 1 (M.val.map f x) :=
      congrArg (fun z ↦ S.obj.map f s • z) hu.symm
    _ = _ := ht

private theorem openTensor_hom_ext
    (M : reductionModules W.left S) (N : reductionModules T R)
    (f g : (cbcRingedOpenExtension W cR).obj
      ((reductionRestrict W.left ψ).obj ((reductionChange W.left ψ).obj M)) ⟶ N)
    (hfg : ∀ (V : T.ProEt) (a : V ⟶ W)
      (s : C.obj.obj (op ((cbcSliceFunctor T W).obj (Over.mk a))))
      (x : M.val.obj (op ((cbcSliceFunctor T W).obj (Over.mk a)))),
      f.val.app (op V) (cbcOpenSection W cR
        ((reductionRestrict W.left ψ).obj ((reductionChange W.left ψ).obj M)) V a
        (reductionTensorSection W.left ψ M
          (op ((cbcSliceFunctor T W).obj (Over.mk a))) s x)) =
      g.val.app (op V) (cbcOpenSection W cR
        ((reductionRestrict W.left ψ).obj ((reductionChange W.left ψ).obj M)) V a
        (reductionTensorSection W.left ψ M
          (op ((cbcSliceFunctor T W).obj (Over.mk a))) s x))) : f = g := by
  apply ((openAdj W cR).homEquiv _ _).injective
  apply level_hom_ext W.left ψ M ((openStar W cR).obj N)
  intro U s x
  rw [openAdj_apply, openAdj_apply]
  erw [tensorSection_restrict]
  exact hfg ((ProEt.sliceFrom T W).obj U.unop).left
    ((ProEt.sliceFrom T W).obj U.unop).hom _ _

end ScalarComparison

section KFlatTransport
variable {T : Scheme.{u}} (W : T.ProEt)
  {R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
  {S : Sheaf (ProEt.topology W.left) CommRingCat.{u + 1}}
  (c : R.over W ≅ cbcSliceRing W S)

private abbrev sliceSetPull :=
  (cbcSliceFunctor T W).sheafPushforwardContinuous (Type (u + 1))
    ((ProEt.topology T).over W) (ProEt.topology W.left)

private abbrev sliceRawModules :=
  SheafOfModules.pushforward.{u + 1} (F := cbcSliceFunctor T W)
    (J := (ProEt.topology T).over W) (K := ProEt.topology W.left)
    (R := reductionModuleRing W.left S)
    (S := (sheafCompose ((ProEt.topology T).over W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (cbcSliceRing W S)) (𝟙 _)

private def sliceAlgebraic :
    SheafOfModules.AlgebraicInverseImage (sliceSetPull W) S (cbcSliceRing W S) where
  ringUnderlying := Iso.refl _
  ringAdd := by intro Q a b z h V x; exact h _ x
  ringMul := by intro Q a b z h V x; exact h _ x
  ringZero := by intro Q a h V x; exact h _ x
  ringOne := by intro Q a h V x; exact h _ x
  modules := sliceRawModules W (S := S)
  moduleUnderlying := Iso.refl _
  moduleAdd := by intro M Q a b z h V x; exact h _ x
  moduleZero := by intro M Q a h V x; exact h _ x
  moduleSMul := by intro M Q a b z h V x; exact h _ x

private def sliceScalar :=
  sliceRawModules W (S := S) ⋙ SheafOfModules.siteCoefficientTensor.{u + 1, u, u + 1} c.inv

private local instance sliceRawModules_additive : (sliceRawModules W (S := S)).Additive := by
  constructor
  intro M N f g
  ext V x
  rfl

private theorem sliceScalarIso : Nonempty (sliceScalar W c ≅ (sliceModules W c).functor) := by
  obtain ⟨θ, _, _, hθ⟩ := SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, u + 1}
    (J := (ProEt.topology T).over W) c.symm
  refine ⟨NatIso.ofComponents (fun M ↦ θ ((sliceRawModules W (S := S)).obj M)) ?_⟩
  intro M N f
  exact hθ _ _ ((sliceRawModules W (S := S)).map f)

private theorem sliceModules_kFlat
    (P : CochainComplex (reductionModules W.left S) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology W.left) (R := S) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R.over W)
      (((sliceModules W c).functor.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := (ProEt.topology T).over W) (R := R.over W)
        ((((sliceModules W c).functor.mapHomologicalComplex (.up ℤ)).obj P).X n) := by
  have : (ProEt.sliceEquiv T W).functor.IsCocontinuous
      ((ProEt.topology T).over W) (ProEt.topology W.left) := sliceFunctor_cocontinuous T W
  have : (ProEt.sliceEquiv T W).functor.IsContinuous
      ((ProEt.topology T).over W) (ProEt.topology W.left) :=
    inferInstanceAs ((cbcSliceFunctor T W).IsContinuous
      ((ProEt.topology T).over W) (ProEt.topology W.left))
  have : (ProEt.sliceEquiv T W).inverse.IsContinuous
      (ProEt.topology W.left) ((ProEt.topology T).over W) :=
    (ProEt.sliceEquiv T W).toAdjunction.isContinuous_of_isCocontinuous
      ((ProEt.topology T).over W) (ProEt.topology W.left)
  let adj := (ProEt.sliceEquiv T W).toAdjunction.sheafPushforwardContinuous
    (E := Type (u + 1)) ((ProEt.topology T).over W) (ProEt.topology W.left)
  have : PreservesFiniteLimits (sliceSetPull W) := by
    exact preservesFiniteLimits_of_reflects_of_preserves _
      (sheafToPresheaf ((ProEt.topology T).over W) (Type (u + 1)))
  have : (sliceScalar W c).Additive := by dsimp only [sliceScalar]; infer_instance
  have h := SheafOfModules.isKFlat_ringedToposPullback
    (sliceSetPull W) _ adj (sliceAlgebraic W (S := S)) c.inv (sliceScalar W c)
    (fun _ ↦ rfl) (fun _ ↦ rfl) P hP hf
  obtain ⟨e₀⟩ := sliceScalarIso W c
  let e := NatIso.mapHomologicalComplex e₀ (.up ℤ)
  exact ⟨SheafOfModules.kFlat_iso_independent (R.over W) (e.app P) h.1,
    fun n ↦ SheafOfModules.flatOnSite_of_iso (R.over W)
      ((HomologicalComplex.eval _ _ n).mapIso (e.app P))
      (h.2 n)⟩
end KFlatTransport

variable {T : Scheme.{u}} (W : T.ProEt) [IsOpenImmersion W.hom]
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

set_option linter.unusedSectionVars false in
/-- The canonical finite identifications preserve every quotient map. -/
theorem cbcQuotientSquare (b a : ℕ) (hab : a ≤ b) :
    CbcOpenRingSquare W (cbcFiniteRestriction W d b) (cbcFiniteRestriction W d a)
      (reductionCoefficientMap T d b a hab) (reductionCoefficientMap W.left d b a hab) := by
  change ((ProEt.topology T).overPullback CommRingCat.{u + 1} W).map
      (reductionCoefficientMap T d b a hab) ≫ cbcFiniteSliceMap d T W a =
    cbcFiniteSliceMap d T W b ≫
      ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{u + 1}
        ((ProEt.topology T).over W) (ProEt.topology W.left)).map
          (reductionCoefficientMap W.left d b a hab)
  rw [finiteSliceMap_eq, finiteSliceMap_eq]
  exact (finiteSliceSystemMap W d).naturality (homOfLE hab).op

set_option linter.unusedSectionVars false in
/-- Completed restriction preserves every finite projection. -/
theorem cbcProjectionSquare (n : ℕ) :
    CbcOpenRingSquare W (cbcCompletedRestriction W d) (cbcFiniteRestriction W d n)
      (completedReductionProjection T d n) (completedReductionProjection W.left d n) := by
  exact ((cbcCompletedSliceMap_exists d T W).exists.choose_spec n).symm

/-- Ordinary open extension with the completed coefficient ring. -/
abbrev cbcCompletedExtension := cbcOpenShriek d W.hom (inferInstance : IsOpenImmersion W.hom)

/-- Additivity inherited from the existing completed open extension. -/
instance cbcCompletedExtension_additive : (cbcCompletedExtension W d).Additive :=
  cbcOpenShriek_additive d W.hom inferInstance

/-- Exactness inherited from the existing completed open extension. -/
instance cbcCompletedExtension_limits : PreservesFiniteLimits (cbcCompletedExtension W d) :=
  cbcOpenShriek_finiteLimits d W.hom inferInstance

/-- Colimit preservation inherited from the existing completed open extension. -/
instance cbcCompletedExtension_colimits : PreservesFiniteColimits (cbcCompletedExtension W d) :=
  cbcOpenShriek_finiteColimits d W.hom inferInstance

/-- Apply the same completed-coefficient extension at every strict tower level. -/
def cbcCompletedTowerExtension :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (cbcCompletedExtension W d)

/-- Exactness on towers is levelwise, including the zero tower. -/
theorem cbcCompletedTowerExtension_exact :
    (cbcCompletedTowerExtension W d).Additive ∧
      PreservesFiniteLimits (cbcCompletedTowerExtension W d) ∧
      PreservesFiniteColimits (cbcCompletedTowerExtension W d) := by
  dsimp only [cbcCompletedTowerExtension]
  exact ⟨inferInstance, ⟨fun _ _ _ ↦ inferInstance⟩, ⟨fun _ _ _ ↦ inferInstance⟩⟩

/-- Additivity on strict towers. -/
instance cbcCompletedTowerExtension_additive : (cbcCompletedTowerExtension W d).Additive :=
  (cbcCompletedTowerExtension_exact W d).1

/-- Preservation of finite limits on strict towers. -/
instance cbcCompletedTowerExtension_limits :
    PreservesFiniteLimits (cbcCompletedTowerExtension W d) :=
  (cbcCompletedTowerExtension_exact W d).2.1

/-- Preservation of finite colimits on strict towers. -/
instance cbcCompletedTowerExtension_colimits :
    PreservesFiniteColimits (cbcCompletedTowerExtension W d) :=
  (cbcCompletedTowerExtension_exact W d).2.2

private def strictDelta (n : ℕ) :=
  openDelta W (cbcCompletedRestriction W d) (cbcFiniteRestriction W d n)
    (completedReductionProjection T d n) (completedReductionProjection W.left d n)
    (cbcProjectionSquare W d n)

private theorem strictDelta_inv_transition
    (M : reductionModules W.left (completedReductionCoefficient W.left d))
    (b a : ℕ) (hab : a ≤ b) :
    (cbcCompletedExtension W d).map ((completedReductionTransition W.left d b a hab).app M) ≫
      (strictDelta W d a).inv.app M =
    (strictDelta W d b).inv.app M ≫
      (completedReductionTransition T d b a hab).app ((cbcCompletedExtension W d).obj M) := by
  apply openTensor_hom_ext W (cbcCompletedRestriction W d)
    (completedReductionProjection W.left d b) M _
  intro V v s x
  have hq := cbcQuotientSquare W d b a hab
  have hi : (cbcFiniteRestriction W d b).inv ≫
      ((ProEt.topology T).overPullback CommRingCat.{u + 1} W).map
        (reductionCoefficientMap T d b a hab) =
      ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{u + 1}
        ((ProEt.topology T).over W) (ProEt.topology W.left)).map
          (reductionCoefficientMap W.left d b a hab) ≫ (cbcFiniteRestriction W d a).inv := by
    apply (cancel_mono (cbcFiniteRestriction W d a).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hq, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hh := congrArg (fun f ↦ f.hom.app (op (Over.mk v)) s) hi
  change (reductionCoefficientMap T d b a hab).hom.app (op V)
      ((cbcFiniteRestriction W d b).inv.hom.app (op (Over.mk v)) s) =
    (cbcFiniteRestriction W d a).inv.hom.app (op (Over.mk v))
      ((reductionCoefficientMap W.left d b a hab).hom.app
        (op ((cbcSliceFunctor T W).obj (Over.mk v))) s) at hh
  let U := op ((cbcSliceFunctor T W).obj (Over.mk v))
  let cR := cbcCompletedRestriction W d
  let τW := (completedReductionTransition W.left d b a hab).app M
  let τT := (completedReductionTransition T d b a hab).app ((cbcCompletedExtension W d).obj M)
  have hmap := openSection_map W cR τW V v
    (reductionTensorSection W.left (completedReductionProjection W.left d b) M U s x)
  have htW := (completedReductionTransition_exists W.left d b a hab).exists.choose_spec M U s x
  have hdA := openDelta_inv W cR (cbcFiniteRestriction W d a)
    (completedReductionProjection T d a) (completedReductionProjection W.left d a)
    (cbcProjectionSquare W d a) M V v
    ((reductionCoefficientMap W.left d b a hab).hom.app U s) x
  have hdB := openDelta_inv W cR (cbcFiniteRestriction W d b)
    (completedReductionProjection T d b) (completedReductionProjection W.left d b)
    (cbcProjectionSquare W d b) M V v s x
  have htT := (completedReductionTransition_exists T d b a hab).exists.choose_spec
    ((cbcCompletedExtension W d).obj M) (op V)
    ((cbcFiniteRestriction W d b).inv.hom.app (op (Over.mk v)) s)
    (cbcOpenSection W cR M V v x)
  have hmap' := hmap.trans (congrArg
    (cbcOpenSection W cR ((completedReductionLevel W.left d a).obj M) V v) htW)
  refine (congrArg (((strictDelta W d a).inv.app M).val.app (op V)) hmap').trans ?_
  refine hdA.trans (Eq.trans ?_ (Eq.trans htT.symm
    (congrArg (τT.val.app (op V)) hdB.symm)))
  exact congrArg (fun z ↦ reductionTensorSection T (completedReductionProjection T d a)
    ((cbcCompletedExtension W d).obj M) (op V) z (cbcOpenSection W cR M V v x)) hh.symm

attribute [local irreducible] strictDelta

private def strictInv :
    completedReductionModuleTowerFunctor W.left d ⋙ cbcCompletedTowerExtension W d ⟶
      cbcCompletedExtension W d ⋙ completedReductionModuleTowerFunctor T d where
  app M := NatTrans.ofOpSequence (fun n ↦ (strictDelta W d n).inv.app M) (by
    intro n
    change (cbcCompletedExtension W d).map
        ((completedReductionModuleTower W.left d M).map (homOfLE (Nat.le_succ n)).op) ≫ _ =
      _ ≫ (completedReductionModuleTower T d ((cbcCompletedExtension W d).obj M)).map
        (homOfLE (Nat.le_succ n)).op
    simp only [completedReductionModuleTower, Functor.ofOpSequence_map_homOfLE_succ]
    exact strictDelta_inv_transition W d M (n + 1) n (Nat.le_succ n))
  naturality := by
    intro M N f
    apply NatTrans.ext
    funext n
    change ((cbcCompletedExtension W d).map ((completedReductionLevel W.left d n.unop).map f)) ≫
      (strictDelta W d n.unop).inv.app N =
      (strictDelta W d n.unop).inv.app M ≫
        (completedReductionLevel T d n.unop).map ((cbcCompletedExtension W d).map f)
    exact (strictDelta W d n.unop).inv.naturality f

private local instance strictInv_isIso : IsIso (strictInv W d) := by
  have (M : reductionModules W.left (completedReductionCoefficient W.left d)) :
      IsIso ((strictInv W d).app M) := by
    have (n : ℕᵒᵖ) : IsIso (((strictInv W d).app M).app n) := by
      change IsIso ((strictDelta W d n.unop).inv.app M)
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

private theorem strictInv_inverse_component
    (M : reductionModules W.left (completedReductionCoefficient W.left d)) (n : ℕ) :
    (((asIso (strictInv W d)).symm.hom.app M).app (op n)) =
      (strictDelta W d n).hom.app M := by
  change ((inv (strictInv W d)).app M).app (op n) = _
  rw [NatIso.isIso_inv_app, NatIso.isIso_inv_app]
  change inv ((strictDelta W d n).inv.app M) = _
  exact NatIso.inv_inv_app (strictDelta W d n) M

attribute [local irreducible] strictInv

/-- The ordinary strict tower comparison is the coefficient-linear comparison followed
by the inverse scalar-restriction comparison at every level. Its naturality is actual
compatibility with all transitions, rather than merely equality in a derived category. -/
theorem cbcStrictReductionIso_existsUnique :
    ∃! δ : cbcCompletedExtension W d ⋙ completedReductionModuleTowerFunctor T d ≅
        completedReductionModuleTowerFunctor W.left d ⋙ cbcCompletedTowerExtension W d,
      ∀ (M : reductionModules W.left (completedReductionCoefficient W.left d)) (n : ℕ),
        (δ.hom.app M).app (op n) =
          (reductionRestrict T (completedReductionProjection T d n)).map
            ((cbcOpenScalarIso W (cbcCompletedRestriction W d) (cbcFiniteRestriction W d n)
              (completedReductionProjection T d n) (completedReductionProjection W.left d n)
              (cbcProjectionSquare W d n)).hom.app M) ≫
          (cbcOpenRestrictIso W (cbcCompletedRestriction W d) (cbcFiniteRestriction W d n)
            (completedReductionProjection T d n) (completedReductionProjection W.left d n)
            (cbcProjectionSquare W d n)).inv.app
              ((reductionChange W.left (completedReductionProjection W.left d n)).obj M) := by
  refine ⟨(asIso (strictInv W d)).symm, ?_, ?_⟩
  · intro M n
    rw [strictInv_inverse_component]
    unfold strictDelta openDelta
    rfl
  · intro δ hδ
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext n
    have hn := strictInv_inverse_component W d M n.unop
    apply (hδ M n.unop).trans
    unfold strictDelta openDelta at hn
    exact hn.symm

/-- The strict comparison with its uniquely prescribed finite-level maps. -/
def cbcStrictReductionIso := (cbcStrictReductionIso_existsUnique W d).exists.choose

section ModelComplex
variable {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
  (F : B ⥤ (ℕᵒᵖ ⥤ B)) [F.Additive] (G : C ⥤ (ℕᵒᵖ ⥤ C)) [G.Additive]
  (P : B ⥤ C) [P.Additive]
  (H : (ℕᵒᵖ ⥤ B) ⥤ (ℕᵒᵖ ⥤ C)) [H.Additive]

/-- The degreewise strict comparison, with the additive category data fixed generically. -/
def cbcModelComplexIso (e : P ⋙ G ≅ F ⋙ H) :=
  NatIso.mapHomologicalComplex e (.up ℤ)

private theorem cbcModelComplexIso_symm_hom (e : P ⋙ G ≅ F ⋙ H) :
    (NatIso.mapHomologicalComplex e.symm (.up ℤ)).hom =
      (cbcModelComplexIso F G P H e).inv := by
  ext K n
  rfl

end ModelComplex

/-- The comparison on actual strict complexes, obtained by applying its module map
in every degree. -/
def cbcStrictReductionComplexIso :=
  @cbcModelComplexIso
    (reductionModules W.left (completedReductionCoefficient W.left d))
    (reductionModules T (completedReductionCoefficient T d)) _ _ _ _
    (completedReductionModuleTowerFunctor W.left d)
    (completedReductionModuleTowerFunctor_additive W.left d)
    (completedReductionModuleTowerFunctor T d)
    (completedReductionModuleTowerFunctor_additive T d)
    (cbcCompletedExtension W d) (cbcCompletedExtension_additive W d)
    (cbcCompletedTowerExtension W d) (cbcCompletedTowerExtension_additive W d)
    (cbcStrictReductionIso W d)

attribute [local irreducible] completedReductionTower Functor.mapDerivedCategory
attribute [local irreducible] Functor.mapDerivedCategoryFactors

noncomputable section ModelComputations
variable {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasDerivedCategory (ℕᵒᵖ ⥤ C)]
  (F : B ⥤ (ℕᵒᵖ ⥤ B)) [F.Additive] (G : C ⥤ (ℕᵒᵖ ⥤ C)) [G.Additive]
  (P : B ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  (H : (ℕᵒᵖ ⥤ B) ⥤ (ℕᵒᵖ ⥤ C)) [H.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (e : P ⋙ G ≅ F ⋙ H)
  (LF : DerivedCategory B ⥤ DerivedCategory (ℕᵒᵖ ⥤ B))
  (LG : DerivedCategory C ⥤ DerivedCategory (ℕᵒᵖ ⥤ C))
  (εF : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (εG : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)

/-- The counit computation for an exact source functor. -/
def cbcModelLeft (K : CochainComplex B ℤ) :=
  LG.map (P.mapDerivedCategoryFactors.hom.app K) ≫
    reductionComplexCounit G LG εG ((P.mapHomologicalComplex (.up ℤ)).obj K)

/-- The counit computation for an exact tower functor. -/
def cbcModelRight (K : CochainComplex B ℤ) :=
  H.mapDerivedCategory.map (reductionComplexCounit F LF εF K) ≫
    H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K)

end ModelComputations

/-- The left endpoint's canonical computation on a representative, using exact open
extension and then the reduction tower's universal counit. -/
def cbcLeftReductionComputation
    (P : CochainComplex (reductionModules W.left
      (completedReductionCoefficient W.left d)) ℤ) :
    ((cbcCompletedExtension W d).mapDerivedCategory ⋙ completedReductionTower T d).obj
        (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((completedReductionComplexTowerFunctor T d).obj
        (((cbcCompletedExtension W d).mapHomologicalComplex (.up ℤ)).obj P)) :=
  @cbcModelLeft
    (reductionModules W.left (completedReductionCoefficient W.left d))
    (reductionModules T (completedReductionCoefficient T d)) _ _ _ _ _ _ _
    (completedReductionModuleTowerFunctor T d)
    (completedReductionModuleTowerFunctor_additive T d)
    (cbcCompletedExtension W d) (cbcCompletedExtension_additive W d)
    (cbcCompletedExtension_limits W d) (cbcCompletedExtension_colimits W d)
    (completedReductionTower T d) (coherenceReductionTowerCounit T d) P

/-- The right endpoint's canonical computation, reducing on the open and extending
its entire strict tower by the exact functor. -/
def cbcRightReductionComputation
    (P : CochainComplex (reductionModules W.left
      (completedReductionCoefficient W.left d)) ℤ) :
    (completedReductionTower W.left d ⋙ (cbcCompletedTowerExtension W d).mapDerivedCategory).obj
        (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((cbcCompletedTowerExtension W d).mapHomologicalComplex (.up ℤ)).obj
        ((completedReductionComplexTowerFunctor W.left d).obj P)) :=
  @cbcModelRight
    (reductionModules W.left (completedReductionCoefficient W.left d))
    (reductionModules T (completedReductionCoefficient T d)) _ _ _ _ _ _ _
    (completedReductionModuleTowerFunctor W.left d)
    (completedReductionModuleTowerFunctor_additive W.left d)
    (cbcCompletedTowerExtension W d) (cbcCompletedTowerExtension_additive W d)
    (cbcCompletedTowerExtension_limits W d) (cbcCompletedTowerExtension_colimits W d)
    (completedReductionTower W.left d) (coherenceReductionTowerCounit W.left d) P

private theorem completedOpen_eq : cbcCompletedExtension W d =
    (sliceModules W (cbcCompletedRestriction W d)).functor ⋙
      SheafOfModules.localizedSystemExtension.{u + 1, u, u + 1}
        (completedReductionCoefficient T d) W := by
  rfl

private theorem completedOpen_kFlat
    (P : CochainComplex (reductionModules W.left
      (completedReductionCoefficient W.left d)) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology W.left)
      (R := completedReductionCoefficient W.left d) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := completedReductionCoefficient T d)
      (((cbcCompletedExtension W d).mapHomologicalComplex (.up ℤ)).obj P) := by
  have h := sliceModules_kFlat W (cbcCompletedRestriction W d) P hP hf
  have hh := (SheafOfModules.ringedOpen_preserves_flat_resolution.{u + 1, u, u + 1}
    (completedReductionCoefficient T d) W).1 _ h.1
  have : (sliceModules W (cbcCompletedRestriction W d)).functor.Additive := by
    constructor
    intro M N f g
    ext V x
    rfl
  have : ((sliceModules W (cbcCompletedRestriction W d)).functor ⋙
      SheafOfModules.localizedSystemExtension.{u + 1, u, u + 1}
        (completedReductionCoefficient T d) W).Additive := by
    infer_instance
  let e₀ : cbcCompletedExtension W d ≅
      (sliceModules W (cbcCompletedRestriction W d)).functor ⋙
        SheafOfModules.localizedSystemExtension.{u + 1, u, u + 1}
          (completedReductionCoefficient T d) W := eqToIso (completedOpen_eq W d)
  let e := (NatIso.mapHomologicalComplex e₀ (.up ℤ)) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).symm
  exact SheafOfModules.kFlat_iso_independent (completedReductionCoefficient T d)
    (e.app P).symm hh

private theorem reverseIsoSquare {D : Type*} [Category D]
    {X Y A B : D} (e : X ≅ Y) (d : A ≅ B) (l : Y ⟶ A) (r : X ⟶ B) :
    e.hom ≫ l = r ≫ d.inv ↔ e.inv ≫ r = l ≫ d.hom := by
  constructor
  · intro h
    apply (cancel_epi e.hom).1
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro h
    apply (cancel_epi e.inv).1
    simp only [Iso.inv_hom_id_assoc]
    rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

noncomputable section ModelReverse
variable {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasDerivedCategory (ℕᵒᵖ ⥤ C)]
  (F : B ⥤ (ℕᵒᵖ ⥤ B)) [F.Additive] (G : C ⥤ (ℕᵒᵖ ⥤ C)) [G.Additive]
  (P : B ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  (H : (ℕᵒᵖ ⥤ B) ⥤ (ℕᵒᵖ ⥤ C)) [H.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (e : P ⋙ G ≅ F ⋙ H)
  (LF : DerivedCategory B ⥤ DerivedCategory (ℕᵒᵖ ⥤ B))
  (LG : DerivedCategory C ⥤ DerivedCategory (ℕᵒᵖ ⥤ C))
  (εF : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (εG : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)

private theorem modelComparison_reverse
    (η : LF ⋙ H.mapDerivedCategory ≅ P.mapDerivedCategory ⋙ LG)
    (K : CochainComplex B ℤ) :
    (η.hom.app (DerivedCategory.Q.obj K) ≫ cbcModelLeft G P LG εG K =
      cbcModelRight F H LF εF K ≫
        DerivedCategory.Q.map (((cbcModelComplexIso F G P H e).symm).hom.app K)) ↔
    (η.inv.app (DerivedCategory.Q.obj K) ≫ cbcModelRight F H LF εF K =
      cbcModelLeft G P LG εG K ≫
        DerivedCategory.Q.map ((cbcModelComplexIso F G P H e).hom.app K)) := by
  let δ := DerivedCategory.Q.mapIso ((cbcModelComplexIso F G P H e).app K)
  change (η.hom.app _ ≫ cbcModelLeft G P LG εG K = cbcModelRight F H LF εF K ≫ δ.inv) ↔
    (η.inv.app _ ≫ cbcModelRight F H LF εF K = cbcModelLeft G P LG εG K ≫ δ.hom)
  exact reverseIsoSquare (η.app (DerivedCategory.Q.obj K)) δ
    (cbcModelLeft G P LG εG K) (cbcModelRight F H LF εF K)

private theorem modelForward_existsUnique
    {M : CochainComplex B ℤ → Prop} {N : CochainComplex C ℤ → Prop}
    (DF : DerivedReductionModelData F M) (DG : DerivedReductionModelData G N)
    (M₀ : CochainComplex B ℤ → Prop) (h₀ : ∀ K, M₀ K → M K)
    (res : ∀ K : CochainComplex B ℤ, ∃ (L : CochainComplex B ℤ) (s : L ⟶ K),
      M₀ L ∧ QuasiIso s)
    (hmap : ∀ K, M₀ K → N ((P.mapHomologicalComplex (.up ℤ)).obj K)) :
    ∃! ρ : P.mapDerivedCategory ⋙ DG.reduction ≅ DF.reduction ⋙ H.mapDerivedCategory,
      ∀ K : CochainComplex B ℤ, M K →
      ρ.hom.app (DerivedCategory.Q.obj K) ≫
          cbcModelRight F H DF.reduction DF.counit K =
        cbcModelLeft G P DG.reduction DG.counit K ≫
          DerivedCategory.Q.map ((cbcModelComplexIso F G P H e).hom.app K) := by
  obtain ⟨η, hη, hu⟩ := OrderedExchange.modelPull_existsUnique
    F G P H DF DG e.symm M₀ h₀ res hmap
  refine ⟨η.symm, ?_, ?_⟩
  · intro K hK
    apply (modelComparison_reverse F G P H e DF.reduction DG.reduction
      DF.counit DG.counit η K).mp
    simpa only [cbcModelComplexIso_symm_hom, Iso.symm_hom, cbcModelLeft, cbcModelRight,
      DerivedReductionModelData.complexCounit,
      reductionComplexCounit, Category.assoc] using hη K hK
  · intro ρ hρ
    have he : ρ.symm = η := by
      apply hu
      intro K hK
      have hh := (modelComparison_reverse F G P H e DF.reduction DG.reduction
        DF.counit DG.counit ρ.symm K).mpr (hρ K hK)
      simpa only [cbcModelComplexIso_symm_hom, Iso.symm_hom, cbcModelLeft, cbcModelRight,
      DerivedReductionModelData.complexCounit,
        reductionComplexCounit, Category.assoc] using hh
    exact congrArg Iso.symm he

private theorem modelForwardCurried_existsUnique
    {M₁ M₂ : CochainComplex B ℤ → Prop} {N : CochainComplex C ℤ → Prop}
    (DF : DerivedReductionModelData F (fun K ↦ M₁ K ∧ M₂ K))
    (DG : DerivedReductionModelData G N)
    (res : ∀ K : CochainComplex B ℤ, ∃ (L : CochainComplex B ℤ) (s : L ⟶ K),
      (M₁ L ∧ M₂ L) ∧ QuasiIso s)
    (hmap : ∀ K, M₁ K → M₂ K → N ((P.mapHomologicalComplex (.up ℤ)).obj K)) :
    ∃! ρ : P.mapDerivedCategory ⋙ DG.reduction ≅ DF.reduction ⋙ H.mapDerivedCategory,
      ∀ K : CochainComplex B ℤ, M₁ K → M₂ K →
      IsIso (cbcModelLeft G P DG.reduction DG.counit K) ∧
      IsIso (cbcModelRight F H DF.reduction DF.counit K) ∧
      ρ.hom.app (DerivedCategory.Q.obj K) ≫
          cbcModelRight F H DF.reduction DF.counit K =
        cbcModelLeft G P DG.reduction DG.counit K ≫
          DerivedCategory.Q.map ((cbcModelComplexIso F G P H e).hom.app K) := by
  obtain ⟨ρ, hρ, hu⟩ := modelForward_existsUnique F G P H e DF DG
    (fun K ↦ M₁ K ∧ M₂ K) (fun _ h ↦ h) res (fun K h ↦ hmap K h.1 h.2)
  refine ⟨ρ, ?_, ?_⟩
  · intro K hK₁ hK₂
    have hK : M₁ K ∧ M₂ K := ⟨hK₁, hK₂⟩
    have : IsIso (reductionComplexCounit F DF.reduction DF.counit K) :=
      DF.complexCounit_isIso K hK
    have : IsIso (reductionComplexCounit G DG.reduction DG.counit
        ((P.mapHomologicalComplex (.up ℤ)).obj K)) :=
      DG.complexCounit_isIso _ (hmap K hK₁ hK₂)
    refine ⟨?_, ?_, hρ K hK⟩
    · dsimp only [cbcModelLeft]
      infer_instance
    · dsimp only [cbcModelRight]
      infer_instance
  · intro σ hσ
    apply hu
    intro K hK
    exact (hσ K hK.1 hK.2).2.2

end ModelReverse

private theorem moduleForward_existsUnique
    (X Y : Scheme.{u})
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (RY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (F : reductionModules X RX ⥤ (ℕᵒᵖ ⥤ reductionModules X RX)) [F.Additive]
    (G : reductionModules Y RY ⥤ (ℕᵒᵖ ⥤ reductionModules Y RY)) [G.Additive]
    (P : reductionModules X RX ⥤ reductionModules Y RY) [P.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (H : (ℕᵒᵖ ⥤ reductionModules X RX) ⥤ (ℕᵒᵖ ⥤ reductionModules Y RY)) [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : P ⋙ G ≅ F ⋙ H)
    (LF : DerivedCategory (reductionModules X RX) ⥤
      DerivedCategory (ℕᵒᵖ ⥤ reductionModules X RX))
    (LG : DerivedCategory (reductionModules Y RY) ⥤
      DerivedCategory (ℕᵒᵖ ⥤ reductionModules Y RY))
    (εF : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (εG : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (M₁ M₂ : CochainComplex (reductionModules X RX) ℤ → Prop)
    (N : CochainComplex (reductionModules Y RY) ℤ → Prop)
    (hLF : LF.IsLeftDerivedFunctor εF
      (HomotopyCategory.quasiIso (reductionModules X RX) (.up ℤ)))
    (hLG : LG.IsLeftDerivedFunctor εG
      (HomotopyCategory.quasiIso (reductionModules Y RY) (.up ℤ)))
    (hF : ∀ K : CochainComplex (reductionModules X RX) ℤ, M₁ K →
      IsIso (εF.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)))
    (hG : ∀ K : CochainComplex (reductionModules Y RY) ℤ, N K →
      IsIso (εG.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)))
    (res : ∀ K : CochainComplex (reductionModules X RX) ℤ,
      ∃ (L : CochainComplex (reductionModules X RX) ℤ) (s : L ⟶ K),
        (M₁ L ∧ M₂ L) ∧ QuasiIso s)
    (hmap : ∀ K, M₁ K → M₂ K → N ((P.mapHomologicalComplex (.up ℤ)).obj K)) :
    ∃! ρ : P.mapDerivedCategory ⋙ LG ≅ LF ⋙ H.mapDerivedCategory,
      ∀ K : CochainComplex (reductionModules X RX) ℤ, M₁ K → M₂ K →
      IsIso (cbcModelLeft G P LG εG K) ∧ IsIso (cbcModelRight F H LF εF K) ∧
      ρ.hom.app (DerivedCategory.Q.obj K) ≫ cbcModelRight F H LF εF K =
        cbcModelLeft G P LG εG K ≫
          DerivedCategory.Q.map ((cbcModelComplexIso F G P H e).hom.app K) := by
  let DF : DerivedReductionModelData F (fun K ↦ M₁ K ∧ M₂ K) :=
    { reduction := LF
      counit := εF
      isLeftDerived := hLF
      isIso_counit := fun K h ↦ hF K h.1 }
  let DG : DerivedReductionModelData G N :=
    { reduction := LG
      counit := εG
      isLeftDerived := hLG
      isIso_counit := hG }
  exact modelForwardCurried_existsUnique F G P H e DF DG res hmap

section DerivedComparisonOpacity

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] cbcOpenShriek cbcCompletedTowerExtension
attribute [local irreducible] completedReductionModuleTowerFunctor cbcStrictReductionIso
attribute [local irreducible] reductionComplexCounit
attribute [local irreducible] coherenceReductionTowerCounit

/-- Canonical natural strict reduction under ringed open extension. Its components
are the desired rho_(e,K). The unique characterization ties them to actual strict
chain maps, not just arbitrary isomorphisms of derived objects. No completeness or
quasi-compactness assumption occurs. -/
theorem cbcRingedOpenStrictReduction :
    ∃! ρ : (cbcCompletedExtension W d).mapDerivedCategory ⋙ completedReductionTower T d ≅
        completedReductionTower W.left d ⋙ (cbcCompletedTowerExtension W d).mapDerivedCategory,
      ∀ (P : CochainComplex (reductionModules W.left
          (completedReductionCoefficient W.left d)) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients
            (R := completedReductionCoefficient W.left d) P →
        (∀ p : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology W.left)
          (R := completedReductionCoefficient W.left d) (P.X p)) →
        IsIso (cbcLeftReductionComputation W d P) ∧
        IsIso (cbcRightReductionComputation W d P) ∧
        ρ.hom.app (DerivedCategory.Q.obj P) ≫ cbcRightReductionComputation W d P =
          cbcLeftReductionComputation W d P ≫
            DerivedCategory.Q.map ((cbcStrictReductionComplexIso W d).hom.app P) := by
  exact @moduleForward_existsUnique W.left T
    (completedReductionCoefficient W.left d) (completedReductionCoefficient T d)
    (completedReductionModuleTowerFunctor W.left d)
    (completedReductionModuleTowerFunctor_additive W.left d)
    (completedReductionModuleTowerFunctor T d)
    (completedReductionModuleTowerFunctor_additive T d)
    (cbcCompletedExtension W d) (cbcCompletedExtension_additive W d)
    (cbcCompletedExtension_limits W d) (cbcCompletedExtension_colimits W d)
    (cbcCompletedTowerExtension W d) (cbcCompletedTowerExtension_additive W d)
    (cbcCompletedTowerExtension_limits W d) (cbcCompletedTowerExtension_colimits W d)
    (cbcStrictReductionIso W d)
    (completedReductionTower W.left d) (completedReductionTower T d)
    (coherenceReductionTowerCounit W.left d) (coherenceReductionTowerCounit T d) _ _ _
    (completedReductionTower_properties W.left d).1
    (completedReductionTower_properties T d).1
    (completedReductionTower_properties W.left d).2.2
    (completedReductionTower_properties T d).2.2
    (OrderedExchange.flatKFlatResolution W.left (completedReductionCoefficient W.left d))
    (fun P hP hf ↦ completedOpen_kFlat W d P hP hf)

end DerivedComparisonOpacity

end AlgebraicGeometry.Scheme
