/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualStrictPullback
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.LowerShriekCoveringGenerators
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.Sites.LowerShriekCorepresentability
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.CategoryTheory.Sites.CoveringRepresentableCoequalizer
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
public import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
public import WeilConjectures.CategoryTheory.InverseMateEquivalence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.NatIso
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
public import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
public import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
public import WeilConjectures.CategoryTheory.ModuleInverseImageAction
public import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
public import WeilConjectures.CategoryTheory.Strict.StrictRoosDerivedLimitComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ImmersionCompletedPullback.SfImmersionCompletedPullbackCoreA
import all WeilConjectures.AlgebraicGeometry.ImmersionCompletedPullback.SfImmersionCompletedPullbackCoreA
import WeilConjectures.AlgebraicGeometry.ImmersionCompletedPullback.SfImmersionFiniteReductionInterval
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.AlgebraicGeometry.Pbc.PbcIntrinsicTowerComplete
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement

import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
import WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.AlgebraicGeometry.Sf.SfImmersionFiniteNormalization
import all WeilConjectures.SmoothPurity.Sf.SfImmersionRoosNormalization
import all WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.CategoryTheory.ExactAdjointTowerModels.ExactAdjointTowerModels
import all WeilConjectures.CategoryTheory.RoosTensor.RoosTensorNormalization
import WeilConjectures.CategoryTheory.UnboundedExactTower.UnboundedExactAdjunctionSquare
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
import all WeilConjectures.CategoryTheory.StrictRoosComparison
import all WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Preadditive.Injective.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.Algebra.Homology.RoosComplex
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all WeilConjectures.CategoryTheory.StrictRoosNormalization
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import all Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import all Mathlib.Basic.Denumerable
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosDescent
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosResolution
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility

/-! # Ordinary immersion pullback and strict completed pullback

Source: localization Step 6; Stacks Tags 09AA, 099M and 099N (2),(5).
The canonical coefficient constructions are reexported from CoreA; strict tower
and Roos constructions remain in this module.
-/

@[expose] public noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section NormalizationProofs

attribute [-instance] CategoryTheory.ringedConstantTowerAdditive
attribute [-instance] CategoryTheory.strictTowerConstantAdditive
attribute [-instance] CategoryTheory.strictTowerLimitAdditive

attribute [local irreducible] AlgebraicGeometry.Scheme.AdicCoefficients.ringSystem
attribute [local irreducible] CategoryTheory.Limits.limit
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale WeilConjectures

namespace ImmersionRoosMateProof
universe v d
open CategoryTheory.RoosTensor
variable {A B : Type (v + 1)} [Category.{v} A] [Category.{v} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
  [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B]
  [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
  [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive] [(lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesLimitsOfShape ℕᵒᵖ F]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)]

end ImmersionRoosMateProof

namespace AlgebraicGeometry.Scheme
namespace ImmersionCompletedPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X Y : Scheme.{u}} (f : Y ⟶ X)

attribute [local irreducible] pbcIntegralDatum

/-- Identify the two strict constructions by their specified augmentation units.
Source: localization Step 6, Steps 2 and 5
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: apply moduleIso levelwise and derive its exact tower functor. The chosen
Rlim functors are the same universal right-derived limit. Their induced comparison
carries the quotient augmentation to itself, giving the displayed equation.
Completion is a reflector into complete objects, so its unit forces uniqueness. -/
theorem strictIso_exists :
    ∃! e : pbcActualStrictCompletedPull (pbcIntegralDatum l E) f ≅
        (pbcIntegralDatum l E).completedPull f,
      ∀ K : PbcCompletedDerived X (pbcIntegralDatum l E),
        (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app K ≫ e.hom.app K =
          (derivedIso l E f).hom.app K ≫ (pbcIntegralDatum l E).ordinaryToCompleted f K := by
  let d := pbcIntegralDatum l E
  let e := cbcDatumActualStrictTransport d f
  have he (K : PbcCompletedDerived X d) :
      (pbcActualStrictCompletedPullUnit d f).app K ≫ e.hom.app K =
        (derivedIso l E f).hom.app K ≫ d.ordinaryToCompleted f K := by
    rw [← ordinary_transport_eq]
    exact cbcDatumActualStrictTransport_unit d f K
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  obtain ⟨α, hα⟩ := strict_completion l E f r a ha K
  have hcomplete := (wfCompletionReflector Y d r a ha).1
    ((pbcActualDerivedPull f d).obj K)
  have hsource : WfIsComplete Y d r a ha
      ((pbcActualStrictCompletedPull d f).obj K) :=
    (wfComplete_iso Y d r a ha α).mpr hcomplete
  have htarget := (wfComplete_iso Y d r a ha (e.app K)).mp hsource
  apply (cancel_epi α.inv).mp
  apply ((wfCompletionReflector Y d r a ha).2 _ _ htarget).injective
  rw [← hα]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (he' K).trans (he K).symm

/-- The unit-normalized identification of the actual strict construction.
Source: localization Step 6, Step 5
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def strictIso := (strictIso_exists l E f).exists.choose

/-- The finite projection of the actual completed pullback, with its finite comparison.
Source: localization Step 6, Step 5
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def actualCompletedProjection
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (n : ℕ) :
    (pbcActualStrictCompletedPull (pbcIntegralDatum l E) f).obj K ⟶
      (restrictedReduction l E Y n).obj
        ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K) :=
  (strictIso l E f).hom.app K ≫ completedProjection l E f K n ≫
    (restrictedComparison l E f n).hom.app K ≫
    (restrictedReduction l E Y n).map ((derivedIso l E f).inv.app K)

/-- The ordinary module inverse image with canonical completed coefficients.
Source: localization Step 6, Step 1
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
abbrev modulePull :
    pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)) ⥤
      pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E)) := proEtaleRingModulePullback f _ _
  ((pbcIntegralDatum l E).integralRingIso f)

/-- Apply the specified ordinary inverse image to all terms of a complex.
Source: localization Step 6, Step 1
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
abbrev complexPull := (modulePull l E f).mapHomologicalComplex (.up ℤ)

/-- Apply the same inverse image to every level and transition of a strict tower complex.
Source: localization Step 6, Steps 2 and 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
abbrev towerComplexPull :=
  ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (modulePull l E f)).mapHomologicalComplex (.up ℤ)

/-- Evaluation commutes with applying inverse image term by term.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: both complexes have inverse image of M_n in every degree and inverse image
of its differential; their chain maps and differential proofs agree by extensionality. -/
theorem complexEvaluation_eq
    (M : CochainComplex (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ)
    (n : ℕ) :
    (complexPull l E f).obj (M.asFunctor.obj (op n)) =
      ((towerComplexPull l E f).obj M).asFunctor.obj (op n) := by
  rfl

/-- The actual product comparison, determined by its projections.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def productComparison
    (M : CochainComplex (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ) :
    (complexPull l E f).obj (strictRoosProduct M) ⟶
      strictRoosProduct ((towerComplexPull l E f).obj M) :=
  Pi.lift (f := fun n : ℕ ↦
    ((towerComplexPull l E f).obj M).asFunctor.obj (op n))
    (fun n : ℕ ↦ (complexPull l E f).map
    (Pi.π (fun k : ℕ ↦ M.asFunctor.obj (op k)) n) ≫
      eqToHom (complexEvaluation_eq l E f M n))

private theorem modulePull_preservesProducts [IsImmersion f] :
    PreservesLimitsOfShape (Discrete ℕ) (modulePull l E f) := by
  obtain ⟨_, _, _, _, _, _, h⟩ :=
    (proEtale_immersion_inverseImage_preservesLimits f).2.2
      ((pbcIntegralDatum l E).completedRing X)
  obtain ⟨P, hobj, hmap, _, _, _, hP⟩ :=
    h ((pbcIntegralDatum l E).completedRing Y) ((pbcIntegralDatum l E).integralRingIso f)
  have he : P = modulePull l E f := CategoryTheory.Functor.ext hobj hmap
  have : PreservesLimitsOfSize.{u + 1, u + 1} (modulePull l E f) := he ▸ hP
  have : PreservesLimitsOfSize.{0, 0} (modulePull l E f) :=
    preservesSmallestLimits_of_preservesLimits _
  infer_instance

/-- The coordinatewise Roos comparison, uniquely normalized by the product map.
Source: localization Step 6, Step 4; Stacks 08TC
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: inverse image preserves countable products for an immersion. Its product
comparison intertwines 1-s, since each projection gives the same pulled-back
transition. In the two Roos coordinates use this comparison on each factor.
The differentials (-dy-(1-s)x,dx) commute with this map; the inverse uses the
inverse product comparison. The coordinates jointly determine the chain map. -/
theorem roosIso_exists [IsImmersion f]
    (M : CochainComplex (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ) :
    ∃! e : (complexPull l E f).obj (strictRoosComplex M) ≅
        strictRoosComplex ((towerComplexPull l E f).obj M),
      ∀ p : ℤ, e.hom.f (p + 1) ≫
          (strictRoosCoordinates ((towerComplexPull l E f).obj M) p).hom =
        (modulePull l E f).map (strictRoosCoordinates M p).hom ≫
          biprodComparison (modulePull l E f) _ _ ≫
            biprod.map ((productComparison l E f M).f p)
              ((productComparison l E f M).f (p + 1)) := by
  have := modulePull_preservesProducts l E f
  have hpc : productComparison l E f M = roosProductComparison (modulePull l E f) M :=
    roos_product_comparison_formula (modulePull l E f) M (complexEvaluation_eq l E f M)
  rw [hpc]
  exact roos_iso_unique (modulePull l E f) M

/-- The strict Roos isomorphism; its data is fixed on both product coordinates.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def roosIso [IsImmersion f]
    (M : CochainComplex (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ) :=
  (roosIso_exists l E f M).exists.choose

/-- A map of strict towers gives the uniquely coordinate-normalized Roos map.
Source: localization Step 6, Step 4; Stacks 08TC
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: naturality intertwines the two transition endomorphisms. Apply the shifted
mapping-cone construction; its two coordinates give the formula and uniqueness. -/
theorem roosMap_exists (T : Scheme.{u})
    {M N : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ}
    (a : M ⟶ N) :
    ∃! b : strictRoosComplex M ⟶ strictRoosComplex N,
      ∀ p : ℤ, b.f (p + 1) ≫ (strictRoosCoordinates N p).hom =
        (strictRoosCoordinates M p).hom ≫
          biprod.map ((strictRoosProductMap a).f p) ((strictRoosProductMap a).f (p + 1)) := by
  refine ⟨roosF.map a, (fun p ↦ roosF_map_χ a p), ?_⟩
  intro b hb
  ext k : 1
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  apply (cancel_mono (strictRoosCoordinates N p).hom).1
  exact (hb p).trans (roosF_map_χ a p).symm

/-- The strict map of the actual shifted Roos cones.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def roosMap (T : Scheme.{u})
    {M N : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ}
    (a : M ⟶ N) := (roosMap_exists l E T a).exists.choose

/-- The limit embeds into Roos by its zero and compatible-sequence coordinates.
Source: localization Step 6, Step 4; Stacks 07KC
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: a compatible sequence is killed by 1-s. Therefore these coordinates commute
with the displayed Roos differential; the coordinates also give uniqueness. -/
theorem roosInclusion_exists (T : Scheme.{u})
    (I : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) :
    ∃! a : limit I.asFunctor ⟶ strictRoosComplex I,
      ∀ p : ℤ, a.f (p + 1) ≫ (strictRoosCoordinates I p).hom =
        biprod.lift 0 ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) := by
  refine ⟨roosι I, (fun p ↦ roosι_χ I p), ?_⟩
  intro a ha
  ext k : 1
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  apply (cancel_mono (strictRoosCoordinates I p).hom).1
  exact (ha p).trans (roosι_χ I p).symm

/-- The compatible-sequence inclusion, fixed on both cone coordinates.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def roosInclusion (T : Scheme.{u})
    (I : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) :=
  (roosInclusion_exists l E T I).exists.choose

/-- The termwise limit and the limit of evaluated complexes have the same projections.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: limits of complexes are computed degreewise. Their universal property in
each degree gives this chain isomorphism and determines it by its projections. -/
theorem termwiseLimitIso_exists (T : Scheme.{u})
    (I : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) :
    ∃! e : (Functor.mapHomologicalComplex
        (completedTowerLimit T ((pbcIntegralDatum l E).completedRing T))
        (.up ℤ)).obj I ≅ limit I.asFunctor,
      ∀ (n : ℕ) (p : ℤ), e.hom.f p ≫ (limit.π I.asFunctor (op n)).f p =
        limit.π (I.X p) (op n) := by
  let c := HomologicalComplex.coneOfHasLimitEval I.asFunctor
  let hc := HomologicalComplex.isLimitConeOfHasLimitEval I.asFunctor
  let e := (limit.isoLimitCone ⟨c, hc⟩).symm
  have he (n : ℕ) (p : ℤ) :
      e.hom.f p ≫ (limit.π I.asFunctor (op n)).f p =
        limit.π (I.X p) (op n) := by
    exact congrArg (fun f ↦ HomologicalComplex.Hom.f f p)
      (limit.isoLimitCone_inv_π ⟨c, hc⟩ (op n))
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply limit.hom_ext
  intro n
  ext p : 1
  exact (he' n.unop p).trans (he n.unop p).symm

/-- The projection-normalized comparison of the two ordinary limit computations.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def termwiseLimitIso (T : Scheme.{u})
    (I : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) :=
  (termwiseLimitIso_exists l E T I).exists.choose

private theorem roosMap_eq (T : Scheme.{u})
    {M N : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ}
    (a : M ⟶ N) : roosMap l E T a = roosF.map a := by
  exact (roosMap_exists l E T a).unique
    (roosMap_exists l E T a).exists.choose_spec (fun p ↦ roosF_map_χ a p)

private theorem quotientEquiv_eq (n : ℕ) :
    quotientEquiv l E n = integralCoefficientULift l E n := by
  exact (quotientEquiv_exists l E n).unique
    (quotientEquiv_exists l E n).exists.choose_spec
    (integralCoefficientULift_exists l E n).exists.choose_spec

end ImmersionCompletedPullback
end AlgebraicGeometry.Scheme

end NormalizationProofs
