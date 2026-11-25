/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.PrincipalConeTower
public import WeilConjectures.CategoryTheory.Ringed.RingedPrincipalLocalTests
import WeilConjectures.AlgebraicGeometry.PrincipalConeKoszulRoosComparison
import WeilConjectures.CategoryTheory.Principal.PrincipalIdealLocalTestCriterion
import WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.CategoryTheory.RingedExtendedCech
import WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.CategoryTheory.RingedCompletionUnit
import WeilConjectures.CategoryTheory.RingedDerivedRestriction
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
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
import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import WeilConjectures.CategoryTheory.RingedIdealGenerators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
import WeilConjectures.CategoryTheory.RingedCechKoszulDualKFlat
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.FiniteFreeZeroHomologyEvaluationIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.RingedCechKoszulHomLimitComparison
import WeilConjectures.CategoryTheory.RingedCechKoszulColimitIso
import WeilConjectures.Algebra.Homology.InternalHom
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
import WeilConjectures.CategoryTheory.RingedKoszulFactorColimit
import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import WeilConjectures.CategoryTheory.RingedKoszulColimitHomOrdinaryLimit
import WeilConjectures.CategoryTheory.RingedHomComplexColimitCone
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.CategoryTheory.RingedKoszulFiniteEvaluation
import WeilConjectures.CategoryTheory.RingedKoszulDualizable
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.CategoryTheory.RingedHomTensorUnitNormalization
import WeilConjectures.CategoryTheory.RingedComplexTensorEvaluation
import WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.RingedKoszulTensorTowerLimitAcyclic
import WeilConjectures.CategoryTheory.RingedKoszulRoosInclusion
import WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement
import WeilConjectures.CategoryTheory.RingedKoszulFiniteHomTower
import WeilConjectures.Algebra.Homology.TelescopeHomRoosArrow
import WeilConjectures.Algebra.Homology.TelescopeColimit
import WeilConjectures.CategoryTheory.SignedDoubleHomCone.SignedDoubleHomConeSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.SplitPerfectTensorKInjective
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.CategoryTheory.ProperBaseChange.ExtendedCechCompletionModelSupplement
import WeilConjectures.CategoryTheory.RingedAugmentedCechRestriction
import WeilConjectures.CategoryTheory.RingedLocalizationFactorRestriction
import WeilConjectures.CategoryTheory.LocalizationRHom.RingedLocalizationRestrictionSupplement
import WeilConjectures.Algebra.Homology.SliceTensorNatural
import WeilConjectures.Algebra.Homology.SliceModuleSheafification
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import all WeilConjectures.CategoryTheory.UnitPowerCompleteness

/-! # The principal cone criterion on a small ringed site
Source: Stacks 0999, 099B, 0A0E and 0941.
(blueprint: lem-pur-principal-cone-small-site-criterion). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
private theorem complete_of_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    {N M : ringedSiteDerived O} (e : N ≅ M)
    (hN : IsLocallyDerivedRingedIdealComplete O I ι N) :
    IsLocallyDerivedRingedIdealComplete O I ι M := by
  intro U f hf
  let H := derivedInternalHom (J.over U) (O.over U)
  exact (hN U f hf).of_iso
    (H.mapIso ((Iso.refl _).prod ((ringedDerivedRestriction O U).mapIso e))).symm
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
set_option hygiene false in
local notation "Rg" => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
set_option hygiene false in
local notation "A" => SheafOfModules.{u} Rg
variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
  [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u} ((Rg).over U))]
  [HasExactLimitsOfShape (Discrete ℕ) A]

attribute [local irreducible] CochainComplex.PrincipalCone.completion
  CochainComplex.PrincipalCone.unit
attribute [local irreducible] principalKoszulRoosUnit roosF koszulTowerComplex koszulTensorTower

/-- Singleton Koszul completion is the normalized principal cone completion.
Source: Stacks 0999, 099B, 0A0E and 0941.
(blueprint: lem-pur-principal-cone-small-site-criterion).
Proof: the image ideal of scalar multiplication has precisely the locally divisible
sections. Apply the singleton Koszul completion reflector to this image ideal, whose
one-element generating list follows from the image factorization. The comparison with
the strict tensor Koszul Roos complex and then the principal cone Roos complex preserves
the degree-zero unit. Transport output completeness across these comparisons. Their
unit equality identifies the reflector's invertibility criterion with the stated one. -/
theorem principalConeSmallSiteCriterion
    (a : (R.obj ⋙ forget CommRingCat).sections) (P : CochainComplex A ℤ) (μ : End P)
    (hμ : ∀ (q : ℤ) (U : Cᵒᵖ) (x : (P.X q).val.obj U),
      (μ.asHom.f q).val.app U x = @SMul.smul _ _ ((P.X q).val.obj U).isModule.toSMul (a.val U) x) :
    principalLocallyComplete.{u, u, u, w} R a
        ((DerivedCategory.Q.{w} (C := A)).obj (CochainComplex.PrincipalCone.completion μ)) ∧
      (principalLocallyComplete.{u, u, u, w} R a ((DerivedCategory.Q.{w} (C := A)).obj P) ↔
        IsIso ((DerivedCategory.Q.{w} (C := A)).map (CochainComplex.PrincipalCone.unit μ))) := by
  let := principalLocalTestSliceDerived R
  let I := image (ringedKoszulScalar R a).asHom
  let ι := image.ι (ringedKoszulScalar R a).asHom
  obtain ⟨D, hC, _, hcrit, _⟩ := ringedKoszulCompletionReflector R 1 (fun _ ↦ a)
    I ι (principal_generators R a)
  let b : (SheafOfModules.unit Rg).sections := ⟨a.val, a.property⟩
  obtain ⟨c, hc⟩ := principalConeKoszulRoosComparison R P a μ hμ
  obtain ⟨d, hd⟩ := principalKoszulRoos_presentation_comparison R b P D
  let e := c ≪≫ d
  have he : (DerivedCategory.Q.{w} (C := A)).map (CochainComplex.PrincipalCone.unit μ) ≫ e.hom =
      D.unit ((DerivedCategory.Q.{w} (C := A)).obj P) := by
    change _ ≫ c.hom ≫ d.hom = _
    rw [← Category.assoc, hc]
    simpa only [b] using hd
  refine ⟨(principalLocallyComplete_iff R a _).mpr
    (complete_of_iso R I ι e.symm (hC _)), ?_⟩
  rw [principalLocallyComplete_iff R a _, ← hcrit, ← he]
  exact isIso_comp_right_iff _ e.hom

end CategoryTheory
