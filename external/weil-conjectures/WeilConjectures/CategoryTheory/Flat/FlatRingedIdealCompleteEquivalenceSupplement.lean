/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedIdealGenerators
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.CategoryTheory.LocalExtendedCechDescription
public import WeilConjectures.CategoryTheory.RingedExtendedCech
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.CategoryTheory.ProperBaseChange.ExtendedCechCompletionModelSupplement
import WeilConjectures.AlgebraicGeometry.FlatRingedCechBaseChange
import WeilConjectures.AlgebraicGeometry.RingedSiteIdeal
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Sites.Subsheaf
import WeilConjectures.CategoryTheory.LocalExtendedCechDescription
import WeilConjectures.CategoryTheory.RingedIdealGenerators
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.CategoryTheory.RingedDerivedRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.RingedExtendedCech
import WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.LocalizationCech.ExtendedLocalizationCechSupplement
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.AlgebraicGeometry.FlatRingedCechBaseChangeQuasiIso
import WeilConjectures.AlgebraicGeometry.RingedScalarExtensionComplexAdjunction
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.FlatRingedCechLocalComparison
import WeilConjectures.Algebra.Homology.LocalizationCech.FlatLocalizationKoszulCohomologyComparisonSupplement
import WeilConjectures.AlgebraicGeometry.RingedIdealQuotientComparison
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.RingTheory.Ideal.Span
import WeilConjectures.Algebra.Homology.SliceModuleSheafification
import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlatLimits
import WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.RingedSliceExtensionPreservesExact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists
import WeilConjectures.CategoryTheory.RingedSliceExtensionReflectsExact
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import WeilConjectures.AlgebraicGeometry.OrderedKoszulHomologyTorsion
import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.CategoryTheory.RingedCompletionUnit
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import Mathlib.Algebra.Homology.Double
import Mathlib.CategoryTheory.Endomorphism
import WeilConjectures.Algebra.Homology.LocalizationCech.FlatLocalizationKoszulHomotopySupplement
import Mathlib.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.CategoryTheory.RingedCechKoszulColimitIso
import WeilConjectures.Algebra.Homology.InternalHom
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
import WeilConjectures.CategoryTheory.RingedKoszulFactorColimit
import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.AlgebraicGeometry.CoefficientHomAugmentation
import WeilConjectures.AlgebraicGeometry.CoefficientHomUnit
import WeilConjectures.Algebra.Homology.ProperBaseChange.RestrictedCoefficientHomComplexSupplement
import WeilConjectures.AlgebraicGeometry.RestrictionLocalCompleteness
import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.LocalCompletenessModels
import WeilConjectures.CategoryTheory.RingedSiteCompleteElement
import WeilConjectures.CategoryTheory.RingedSiteLocalization
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.CategoryTheory.LocalCoefficientLocalization
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
import WeilConjectures.CategoryTheory.SliceAwayLocalizationFreeResolution
import WeilConjectures.CategoryTheory.SliceAwayLocalization
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.AlgebraicGeometry.RestrictionSectionCompleteness
import WeilConjectures.AlgebraicGeometry.RestrictionDerivedProducts
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.DerivedCategory.AdjointFunctors
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.CategoryTheory.DerivedCategory.EverywhereDefinedDerivedFunctors
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.AlgebraicGeometry.LocalHomTowerCriterion
import WeilConjectures.Algebra.Homology.LocalCoefficientTelescopeDual
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct
import WeilConjectures.CategoryTheory.SequentialTelescopeMono
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Module.ULift
import WeilConjectures.RingTheory.ModuleLocalizationTowerVanishing
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementsIdeal
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementMultiplication
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import WeilConjectures.Algebra.Homology.HomTensorTotal
import WeilConjectures.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementAddition
import WeilConjectures.CategoryTheory.RingedSiteLocalizationCech
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.RingTheory.TwoLocalizationExact
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.CategoryTheory.RingedSiteCompleteElementsLocal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import WeilConjectures.AlgebraicGeometry.RestrictedCoefficientHom
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.AlgebraicGeometry.FlatRingedIdealCompleteEquivalence

/-!
# Flat ringed-site equivalence on locally derived complete objects

Source: Stacks Project, Algebraization, Tags 099I and 0999
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence).
-/

@[expose] public section
set_option Elab.async false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [local instance 20000] ringedCompletionHasSheafCompose

-- All computations with the chosen Hom complex use its public projection API.
attribute [local irreducible] homComplexFunctor ringedHomUnitEvaluationIso

/-- Restriction of scalars preserves small limits, in particular the products in Hom complexes.
Source: Stacks Project, Algebraization, Tag 099I, the construction of E prime
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence).
Proof: compose with the faithful forgetful functor to additive presheaves. Both
forgetful functors preserve small limits, and this composite is the same over B.
The forgetful composite reflects isomorphisms and therefore reflects limits.
Reflection then gives preservation of limits by restriction itself. -/
theorem siteRestrictScalars_preservesLimits
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    PreservesLimitsOfSize.{u, u} (SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)) := by
  let F := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let G := SheafOfModules.forget.{u} (siteModuleRings R) ⋙
    PresheafOfModules.toPresheaf.{u} (siteModuleRings R).obj
  have : PreservesLimitsOfSize.{u, u} (F ⋙ G) :=
    inferInstanceAs (PreservesLimitsOfSize.{u, u}
      (SheafOfModules.forget.{u} (siteModuleRings B) ⋙
        PresheafOfModules.toPresheaf.{u} (siteModuleRings B).obj))
  have : ReflectsLimitsOfSize.{u, u} G := reflectsLimits_of_reflectsIsomorphisms
  exact preservesLimits_of_reflects_of_preserves F G

private theorem locallyDerivedRingedIdealComplete_of_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [∀ U : C, HasDerivedCategory.{w}
      (SheafOfModules.{u} (siteModuleRings (R.over U)))]
    {M N : ringedSiteDerived R} (e : M ≅ N)
    (hN : IsLocallyDerivedRingedIdealComplete R I.module I.inclusion N) :
    IsLocallyDerivedRingedIdealComplete R I.module I.inclusion M := by
  intro U f hf
  exact (hN U f hf).of_iso ((derivedInternalHom (J.over U) (R.over U)).mapIso
    ((Iso.refl _).prod ((ringedDerivedRestriction R U).mapIso e)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
-- The localization comparison contains both product variables and resolution functors.
set_option backward.isDefEq.respectTransparency false in
private theorem ringedDerivedHomUnit_Q_obj
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings O))]
    (M : ringedSiteComplex O) :
    let A := SheafOfModules.{u} (siteModuleRings O)
    letI : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
    let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
    let η := CochainComplex.toKInjectiveResolution.{u} A
    let Q := DerivedCategory.Q (C := A)
    let c := Localization.fac
      ((𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := O)) ⋙ Q)
      (derivedInternalHom_inverts J O I η (fun M ↦
        ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2,
          CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M⟩))
      (Q.op.prod Q)
    ringedDerivedHomUnit O (Q.obj M) =
      Q.map (η.app M) ≫ (Q.mapIso (ringedHomUnitEvaluationIso O (I.obj M))).inv ≫
        c.inv.app (Opposite.op (ringedSiteRingComplex O), M) := by
  let A := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let Q := DerivedCategory.Q (C := A)
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  let H := derivedInternalHom J O
  let F := ringedCechCompletionFunctor O (ringedSiteRingComplex O)
  let c := Localization.fac
    ((𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := O)) ⋙ Q)
    (derivedInternalHom_inverts J O I η (fun M ↦
      ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} _ M⟩))
    (Q.op.prod Q)
  let a : (homComplexFunctor (R := O)).obj
      (Opposite.op (ringedSiteRingComplex O)) ≅ 𝟭 _ :=
    NatIso.ofComponents (ringedHomUnitEvaluationIso O) (by
      intro M N f
      exact ringedHomUnitEvaluationIso_naturality O f)
  let v : Q ⋙ F ≅ I ⋙ (homComplexFunctor (R := O)).obj
      (Opposite.op (ringedSiteRingComplex O)) ⋙ Q :=
    NatIso.ofComponents (fun M ↦ c.app (Opposite.op (ringedSiteRingComplex O), M)) (by
      intro M N f
      have hc := c.hom.naturality
        (X := (Opposite.op (ringedSiteRingComplex O), M))
        (Y := (Opposite.op (ringedSiteRingComplex O), N)) (𝟙 _, f)
      dsimp at hc
      simp only [Functor.map_id, NatTrans.id_app, Category.id_comp, op_id] at hc
      change H.map
          (X := (Opposite.op (Q.obj (ringedSiteRingComplex O)), Q.obj M))
          (Y := (Opposite.op (Q.obj (ringedSiteRingComplex O)), Q.obj N))
          (𝟙 _, Q.map f) ≫ c.hom.app (Opposite.op (ringedSiteRingComplex O), N) =
        c.hom.app (Opposite.op (ringedSiteRingComplex O), M) ≫
          Q.map (((homComplexFunctor (R := O)).obj
            (Opposite.op (ringedSiteRingComplex O))).map (I.map f))
      exact hc)
  let t : Q ⋙ 𝟭 _ ⟶ Q ⋙ F :=
    Functor.whiskerRight η Q ≫
      Functor.whiskerRight (Functor.whiskerLeft I a.inv) Q ≫ v.inv
  let W := HomologicalComplex.quasiIso A (ComplexShape.up ℤ)
  let full := Localization.fullyFaithfulWhiskeringLeft Q W (DerivedCategory A)
  let d : 𝟭 (DerivedCategory A) ⟶ F := full.preimage t
  have hd (M : CochainComplex A ℤ) : d.app (Q.obj M) = t.app M :=
    congrArg (fun z ↦ z.app M) (full.map_preimage t)
  have hu (X : ringedSiteDerived O) : ringedDerivedHomUnit O X = d.app X := by
    let e := Q.objObjPreimageIso X
    have hn := d.naturality e.hom
    dsimp at hn
    rw [← cancel_epi e.hom]
    rw [hn, hd]
    simp only [ringedDerivedHomUnit, t, v, a, e, Q, I, η, c,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  exact (hu (Q.obj M)).trans (hd M)

-- Computing the unit unfolds the product localization and its chosen resolution.
set_option backward.isDefEq.respectTransparency false in
private theorem ringedCechCompletionUnit_Q_obj
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    (K : ringedSiteComplex R) (ε : K ⟶ ringedSiteRingComplex R)
    (M : ringedSiteComplex R) :
    let A := SheafOfModules.{u} (siteModuleRings R)
    letI : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
    let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
    let η := CochainComplex.toKInjectiveResolution.{u} A
    let Q := DerivedCategory.Q (C := A)
    let c : Q.op.prod Q ⋙ derivedInternalHom J R ≅
        (𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ Q :=
      Localization.fac
      ((𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ Q)
      (derivedInternalHom_inverts J R I η (fun M ↦
        ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2,
          CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M⟩))
      (Q.op.prod Q)
    ringedCechCompletionUnit R K ε (Q.obj M) =
      Q.map (η.app M ≫ (ringedHomUnitEvaluationIso R (I.obj M)).inv ≫
        ((homComplexFunctor (R := R)).map ε.op).app (I.obj M)) ≫
          c.inv.app (Opposite.op K, M) := by
  let A := SheafOfModules.{u} (siteModuleRings R)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  let Q := DerivedCategory.Q (C := A)
  let c : Q.op.prod Q ⋙ derivedInternalHom J R ≅
      (𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ Q :=
    Localization.fac
    ((𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ Q)
    (derivedInternalHom_inverts J R I η (fun M ↦
      ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2,
        CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M⟩))
    (Q.op.prod Q)
  change ringedCechCompletionUnit R K ε (Q.obj M) =
    Q.map (η.app M ≫ (ringedHomUnitEvaluationIso R (I.obj M)).inv ≫
      ((homComplexFunctor (R := R)).map ε.op).app (I.obj M)) ≫
        c.inv.app (Opposite.op K, M)
  have hc := c.inv.naturality (X := (Opposite.op (ringedSiteRingComplex R), M))
    (Y := (Opposite.op K, M)) (ε.op, 𝟙 M)
  dsimp at hc
  simp only [Functor.map_id, Category.comp_id] at hc
  unfold ringedCechCompletionUnit
  have hu := ringedDerivedHomUnit_Q_obj R M
  change ringedDerivedHomUnit R (Q.obj M) =
    Q.map (η.app M) ≫ Q.map (ringedHomUnitEvaluationIso R (I.obj M)).inv ≫
      c.inv.app (Opposite.op (ringedSiteRingComplex R), M) at hu
  rw [hu]
  simp only [Functor.map_comp, Category.assoc]
  rw [← hc]

set_option backward.isDefEq.respectTransparency false in
private theorem derivedCoefficientHomFunctor
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings B))]
    (L : ringedSiteComplex B)
    (G : ringedSiteComplex R ⥤ ringedSiteComplex B)
    (c : G ⋙ (SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex
          (.up ℤ) ≅
      (homComplexFunctor (R := R)).obj
        (Opposite.op (((SheafOfModules.restrictScalars.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapHomologicalComplex
            (.up ℤ)).obj L))) :
    let A := SheafOfModules.{u} (siteModuleRings R)
    letI : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
    let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
    let QR := DerivedCategory.Q (C := A)
    let QB := DerivedCategory.Q (C := SheafOfModules.{u} (siteModuleRings B))
    ∃ (F : ringedSiteDerived R ⥤ ringedSiteDerived B),
      Nonempty (QR ⋙ F ≅ I ⋙ G ⋙ QB) := by
  let A := SheafOfModules.{u} (siteModuleRings R)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let r := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let := (siteRestrictScalars_exact φ).1
  let := (siteRestrictScalars_exact φ).2
  let rc := r.mapHomologicalComplex (.up ℤ)
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  let QR := DerivedCategory.Q (C := A)
  let QB := DerivedCategory.Q (C := SheafOfModules.{u} (siteModuleRings B))
  let H := (homComplexFunctor (R := R)).obj (Opposite.op (rc.obj L))
  let cL : G ⋙ rc ≅ H := c
  have hinv : (HomologicalComplex.quasiIso A (.up ℤ)).IsInvertedBy
      (I ⋙ G ⋙ QB) := by
    intro M N f hf
    have : QuasiIso f := hf
    have : QuasiIso (η.app M) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2
    have : QuasiIso (η.app N) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A N).2
    have hη : QuasiIso (η.app M ≫ I.map f) := by
      rw [← η.naturality f]
      dsimp
      infer_instance
    have : QuasiIso (I.map f) := (quasiIso_iff_comp_left _ _).mp hη
    have : (I.obj M).IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M
    have : (I.obj N).IsKInjective :=
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A N
    have hh : QuasiIso (H.map (I.map f)) := by
      simpa [H] using quasiIso_homComplex_map (I.map f) (𝟙 (rc.obj L))
    have hr : QuasiIso (rc.map ((G).map (I.map f))) := by
      exact (quasiIso_iff_of_arrow_mk_iso
        (rc.map ((G).map (I.map f))) (H.map (I.map f))
        (Arrow.isoMk (cL.app (I.obj M)) (cL.app (I.obj N))
          (cL.hom.naturality (I.map f)).symm)).mpr hh
    have : QuasiIso ((G).map (I.map f)) :=
      (siteRestrictScalars_quasiIso_iff φ _).mp hr
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr inferInstance
  let F := Localization.lift (I ⋙ G ⋙ QB) hinv QR
  let fF := Localization.fac (I ⋙ G ⋙ QB) hinv QR
  exact ⟨F, ⟨fF⟩⟩

-- The localization comparison involves three resolutions and several whiskered isomorphisms.
end CategoryTheory
