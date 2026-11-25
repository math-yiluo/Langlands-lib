/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedEquivalence
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteProetaleStrictTowerRealization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
import WeilConjectures.CategoryTheory.StrictRoosComparison
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.Algebra.Homology.RoosComplex
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
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
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.StrictRoosNormalization
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.Basic.Denumerable
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosDescent
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosResolution
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenExtensionProducts
import WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction
import WeilConjectures.Algebra.Homology.SequenceProjection.SequencePushforwardLimitProjections
import WeilConjectures.CategoryTheory.Diagram.DiagramRingRestrictionPushforward
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison

/-!
# Complete compactification images and strict coefficient limits

Source: blueprint, sec-smooth-purity/sk-prop-sp-integral-adjunction,
direct-image proof, paragraph (2)
(blueprint: def-sp-complete-compactification-limit-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u a b c va vb vc
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.CompleteCompactificationLimit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Ordinary unbounded modules over the completed integral coefficient sheaf.
Source: blueprint paragraph (2)
(blueprint: def-sp-complete-compactification-limit-comparison). -/
abbrev Integral (T : Scheme.{u}) := DerivedCategory (scalarReductionSource l E T)

/-- Fixed completed-coefficient strict towers, before localization.
Source: blueprint paragraph (2), restriction before limit
(blueprint: def-sp-complete-compactification-limit-comparison). -/
abbrev Fixed (T : Scheme.{u}) := ℕᵒᵖ ⥤ scalarReductionSource l E T

/-- The actual open extension over the completed coefficient sheaf.
Source: blueprint paragraph (2), separately derived compactification
(blueprint: def-sp-complete-compactification-limit-comparison). -/
abbrev openOrd {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :=
  PurCompactSupport.openExtension (PurCompactSupport.completed l E) j

/-- The actual ordinary ringed direct image over the completed coefficient sheaf.
Source: blueprint paragraph (2)
(blueprint: def-sp-complete-compactification-limit-comparison). -/
abbrev pushOrd {Z Y : Scheme.{u}} (p : Z ⟶ Y) :=
  proEtaleRingModuleDirectImage p ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring Z) ((PurCompactSupport.completed l E).pull p)

/-- Open extension of fixed-ring strict towers, retaining every transition.
Source: blueprint paragraph (2), strict-tower comparison
(blueprint: def-sp-complete-compactification-limit-comparison). -/
abbrev fixedOpenOrd {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (openOrd l E j)

/-- Direct image of fixed-ring strict towers, before right derivation.
Source: blueprint paragraph (2), strict-tower comparison
(blueprint: def-sp-complete-compactification-limit-comparison). -/
abbrev fixedPushOrd {Z Y : Scheme.{u}} (p : Z ⟶ Y) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pushOrd l E p)

/-- Canonical direct-image/Rlim comparison, obtained by conjugating the identity
constant-tower/pullback square through the actual geometric and limit adjunctions.
Source: blueprint paragraph (2); Stacks 0A07
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def pushLimit {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    coefficientConstantTowerLimit l E Z ⋙ (pushOrd l E p).rightDerivedFunctor ≅
      (fixedPushOrd l E p).rightDerivedFunctor ⋙ coefficientConstantTowerLimit l E Y :=
  conjugateIsoEquiv
    ((proEtaleRingDerivedAdjunction p ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring Z)
      ((PurCompactSupport.completed l E).pull p)).comp
        (cbcRealizationLimitAdj Z ((PurCompactSupport.completed l E).ring Z)))
    ((cbcRealizationLimitAdj Y ((PurCompactSupport.completed l E).ring Y)).comp
      (((proEtaleRingModuleAdjunction p ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring Z)
        ((PurCompactSupport.completed l E).pull p)).whiskerRight
          ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction))
    (cbcRealizationConst (proEtaleRingModulePullback p
      ((PurCompactSupport.completed l E).ring Y) ((PurCompactSupport.completed l E).ring Z)
      ((PurCompactSupport.completed l E).pull p))).symm

/-- The positive ell-power quotient rings, in the existing coefficient universe.
Source: blueprint coefficient convention
(blueprint: def-sp-complete-compactification-limit-comparison). -/
abbrev rings (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n))

/-- The actual quotient maps, starting at exponent one.
Source: blueprint coefficient convention
(blueprint: def-sp-complete-compactification-limit-comparison). -/
abbrev transitions (n : ℕ) : rings l E (n + 1) ⟶ rings l E n :=
  CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((Ideal.Quotient.factorPowSucc (spEllIdeal l E) (n + 1)).comp
      ULift.ringEquiv.toRingHom))

/-- The same finite coefficient sheaves with their constant-section pullback maps.
Source: blueprint paragraph (2), finite coefficient identifications
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def finiteCoefficients (n : ℕ) : PurCompactSupport.Coefficients.{u} where
  ring T := (spCoefficientCommRings.{u, u} l E T).obj (op n)
  pull f := StrictTower.constantRingIso (rings l E n) f

/-- Canonical comparison between the finite open presentations, preserving the open unit.
Source: Stacks 03DI; blueprint paragraph (2)
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def finiteOpen (b : SpTowerShriek.Base l E) {X Z : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (n : ℕ) :
    PurCompactSupport.openExtension (finiteCoefficients.{u} l E n) j ≅
      sfIntrinsicExtensionByZero j (SpTowerShriek.R l E n) :=
  letI := b.finite n
  (PurCompactSupport.openAdjunction (finiteCoefficients.{u} l E n) j).leftAdjointUniq
    ((SpTowerShriek.finiteOpenAdjunction l E b j n))

/-- Canonical reduction to the recorded strict coefficient category.
Source: blueprint paragraph (2), r_T
(blueprint: def-sp-complete-compactification-limit-comparison). -/
abbrev reduction (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) := spCompletedReduction l E T D r

/-- Exact scalar forgetting, before passage to the derived category.
Source: blueprint paragraph (2), U_T
(blueprint: def-sp-complete-compactification-limit-comparison). -/
abbrev forgetting (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T) :=
  spCompletedStrictTower l E T D

/-- The same ordinary strict open functor, prior to localization.
Source: blueprint paragraph (2), termwise scalar normalization
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def ordinaryTowerOpen (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :=
  (b.realization X).functor ⋙ (o.openOp j).extension ⋙ (b.realization Z).inverse

/-- The same ordinary strict direct image, prior to derivation.
Source: blueprint paragraph (2), termwise scalar normalization
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def ordinaryTowerPush (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) :=
  (b.realization Z).functor ⋙ (o.geometry p).push ⋙ (b.realization Y).inverse

/-- Additivity of the actual transported open functor.
Source: blueprint paragraph (2)
(blueprint: def-sp-complete-compactification-limit-comparison). -/
instance ordinaryTowerOpenAdditive (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] : (ordinaryTowerOpen l E b o j).Additive :=
  letI := b.realizationAdditive X
  letI := Functor.additive_of_preserves_binary_products (b.realization Z).inverse
  show ((b.realization X).functor ⋙ (o.openOp j).extension ⋙
    (b.realization Z).inverse).Additive from inferInstance

/-- Exactness of transported open extension on strict systems.
Source: blueprint paragraph (2)
(blueprint: def-sp-complete-compactification-limit-comparison). -/
instance ordinaryTowerOpenLimits (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] : PreservesFiniteLimits (ordinaryTowerOpen l E b o j) :=
  show PreservesFiniteLimits ((b.realization X).functor ⋙ (o.openOp j).extension ⋙
    (b.realization Z).inverse) from inferInstance

/-- Cokernel preservation of transported open extension.
Source: blueprint paragraph (2)
(blueprint: def-sp-complete-compactification-limit-comparison). -/
instance ordinaryTowerOpenColimits (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] : PreservesFiniteColimits (ordinaryTowerOpen l E b o j) :=
  show PreservesFiniteColimits ((b.realization X).functor ⋙ (o.openOp j).extension ⋙
    (b.realization Z).inverse) from inferInstance

/-- Additivity of the actual transported direct image.
Source: blueprint paragraph (2)
(blueprint: def-sp-complete-compactification-limit-comparison). -/
instance ordinaryTowerPushAdditive (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    (ordinaryTowerPush l E b o p).Additive :=
  letI := b.realizationAdditive Z
  letI := Functor.additive_of_preserves_binary_products (b.realization Y).inverse
  show ((b.realization Z).functor ⋙ (o.geometry p).push ⋙
    (b.realization Y).inverse).Additive from inferInstance

/-- Exact open extension of strict systems, localized only after its construction.
Source: blueprint paragraph (2), j_!,bullet
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def towerOpen (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (DX : SpCoefficientTowersAbelian l E X) (DZ : SpCoefficientTowersAbelian l E Z) :=
  letI := DX.hasDerived
  letI := DZ.hasDerived
  (ordinaryTowerOpen l E b o j).mapDerivedCategory

/-- Total right derivation of the simultaneous direct image of strict systems.
Source: blueprint paragraph (2), Rp_*,bullet
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def towerPush (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (DZ : SpCoefficientTowersAbelian l E Z) (DY : SpCoefficientTowersAbelian l E Y) :=
  letI := DZ.hasDerived
  letI := DY.hasDerived
  letI := DZ.grothendieck
  (ordinaryTowerPush l E b o p).rightDerivedFunctor

/-- The specified coefficient compatibility square for every quotient.
Source: blueprint paragraph (2), scalar restriction comparisons
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def ScalarSquares : Prop :=
  ∀ n : ℕ, ∃ a : PurCompactSupport.Change (PurCompactSupport.completed.{u} l E)
      (finiteCoefficients.{u} l E n),
    ∀ T : Scheme.{u}, a.map T = spCompletedEllCommProjection.{u} l E T n

/-- The existing completed-to-quotient scalar map, with the compatibility proof supplied.
Source: blueprint paragraph (2), restriction of finite scalars
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def coefficientChange (h : ScalarSquares l E) (n : ℕ) :
    PurCompactSupport.Change (PurCompactSupport.completed l E) (finiteCoefficients.{u} l E n) :=
  { map := fun T ↦ spCompletedEllCommProjection l E T n
    square := fun f ↦ by
      obtain ⟨a, ha⟩ := h n
      simpa only [← ha] using a.square f }

/-- The actual ordinary integral-to-quotient reduction before localization.
Source: blueprint paragraph (2), actual quotient augmentation
(blueprint: def-sp-complete-compactification-limit-comparison). -/
abbrev ordinaryReduction (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) :=
  restrictScalars ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map r.coefficient.hom) ⋙ r.ordinary

/-- Additivity of the transported ordinary tensor reduction.
Source: blueprint paragraph (2), ordinary tensor construction
(blueprint: def-sp-complete-compactification-limit-comparison). -/
instance ordinaryReductionAdditive (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) : (ordinaryReduction l E T D r).Additive :=
  letI := r.additive
  show (restrictScalars ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map r.coefficient.hom) ⋙
      r.ordinary).Additive from inferInstance

/-- The exact evaluation/localization comparison of the already recorded tower category.
Source: blueprint paragraph (2), exact evaluations
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def finiteEvaluationFactors (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (n : ℕ) :=
  letI := D.hasDerived
  letI := D.equivalenceAdditive
  letI := D.evaluationLimits n
  letI := D.evaluationColimits n
  letI : (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    Functor.additive_of_preserves_binary_products _
  (spCoefficientEvaluation l E T D.equivalence n).mapDerivedCategoryFactors

/-- The universal reduction counit, transported along the recorded coefficient isomorphism.
Source: blueprint paragraph (2), the actual derived tensor construction
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def reductionCounit (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (P : CochainComplex (scalarReductionSource l E T) ℤ) :=
  let F := restrictScalars ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map r.coefficient.hom)
  r.red.map (F.mapDerivedCategoryFactors.hom.app P) ≫
    r.counit.app ((F.mapHomologicalComplex (.up ℤ)).obj P)

/-- The exact scalar-forgetting and normalized reduction-limit presentation.
All structure fields specify already recorded functors and actual quotient units.
Source: blueprint paragraph (2); Stacks 0941, 09T5
(blueprint: def-sp-complete-compactification-limit-comparison). -/
structure LimitPresentation (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) where
  [additive : (forgetting l E T D).Additive]
  [limits : PreservesFiniteLimits (forgetting l E T D)]
  [colimits : PreservesFiniteColimits (forgetting l E T D)]
  adjunction : reduction l E T D r ⊣ spCompletedTotalLimit l E T D
  evaluation : ∀ n : ℕ, reduction l E T D r ⋙ spDerivedCoefficientEvaluation l E T D n ≅
    (D.scalar (spCompletedEllCommProjection l E T n)).model.T
  ordinaryEvaluation : ∀ n : ℕ, ordinaryReduction l E T D r ⋙
    spCoefficientEvaluation l E T D.equivalence n ≅
      (D.scalar (spCompletedEllCommProjection l E T n)).model.E
  tensor_normalized : ∀ (n : ℕ) (M : scalarReductionSource l E T) (U : T.ProEtᵒᵖ)
    (c : ((spCoefficientCommRings l E T).obj (op n)).obj.obj U) (x : M.val.obj U),
    HEq (((ordinaryEvaluation n).hom.app M).val.app U
      (spReductionGenerator l E T D r.coefficient r.ordinary r.level
        ((restrictScalars ((sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            r.coefficient.hom)).obj M) n U c x))
      (systemModelTmul (D.scalar (spCompletedEllCommProjection l E T n)).model M U c x)
  evaluation_normalized : ∀ (n : ℕ) (P : CochainComplex (scalarReductionSource l E T) ℤ),
    (evaluation n).hom.app (DerivedCategory.Q.obj P) ≫
      (D.scalar (spCompletedEllCommProjection l E T n)).model.ε.app P =
    (spDerivedCoefficientEvaluation l E T D n).map (reductionCounit l E T D r P) ≫
      (finiteEvaluationFactors l E T D n).hom.app
        (((ordinaryReduction l E T D r).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (ordinaryEvaluation n) (.up ℤ)).hom.app P)
  unit_projection : ∀ (M : Integral l E T) (n : ℕ),
    adjunction.unit.app M ≫
        (spCompletedTotalProjection l E T D n).app ((reduction l E T D r).obj M) =
      (D.scalar (spCompletedEllCommProjection l E T n)).adjunction.unit.app M ≫
        (spCompletedEllRestriction l E T n).mapDerivedCategory.map
          ((evaluation n).inv.app M)

/-- The specified total limit, after exact restriction of finite scalar actions.
Source: blueprint paragraph (2), L_T
(blueprint: def-sp-complete-compactification-limit-comparison). -/
abbrev totalLimit (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (a : LimitPresentation l E T D r) :=
  letI := a.additive
  letI := a.limits
  letI := a.colimits
  spCompletedTotalLimit l E T D

/-- The normalized finite open comparison, restricted back to completed scalars.
Source: blueprint paragraph (2); Stacks 03DI, 03DJ
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def openScalar (b : SpTowerShriek.Base l E) (h : ScalarSquares l E)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (n : ℕ) :=
  letI := b.finite n
  letI := sfIntrinsicExtensionByZero_additive j (SpTowerShriek.R l E n)
  letI := sfIntrinsicExtensionByZero_preservesFiniteLimits j (SpTowerShriek.R l E n)
  letI := sfIntrinsicExtensionByZero_preservesFiniteColimits j (SpTowerShriek.R l E n)
  PurCompactSupport.openRestriction (coefficientChange l E h n) j ≪≫
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso (finiteOpen l E b j n))
      (spCompletedEllRestriction l E Z n).mapDerivedCategory

/-- The normalized finite direct-image comparison, in the inverse direction of the
recorded restriction/direct-image comparison.
Source: blueprint paragraph (2); Stacks 0D6E
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def pushScalar (h : ScalarSquares l E) {Z Y : Scheme.{u}} (p : Z ⟶ Y) (n : ℕ) :=
  (proEtaleRingRestrictionDerivedDirectImage p
    ((PurCompactSupport.completed l E).ring Y) ((finiteCoefficients l E n).ring Y)
    ((PurCompactSupport.completed l E).ring Z) ((finiteCoefficients l E n).ring Z)
    ((coefficientChange l E h n).map Y) ((coefficientChange l E h n).map Z)
    ((PurCompactSupport.completed l E).pull p) ((finiteCoefficients l E n).pull p)
    ((coefficientChange l E h n).square p)).symm

/-- Exact scalar forgetting on ordinary unbounded derived strict systems.
Source: blueprint paragraph (2)
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def forgetDerived (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (a : LimitPresentation l E T D r) :
    spDerivedCoefficientTowers l E T D ⥤ DerivedCategory (Fixed l E T) :=
  letI := D.hasDerived
  letI := a.additive
  letI := a.limits
  letI := a.colimits
  (forgetting l E T D).mapDerivedCategory

/-- The actual completion unit of the specified scalar-normalized adjunction.
Source: blueprint paragraph (2), eta
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def completionUnit (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (a : LimitPresentation l E T D r) :
    𝟭 (Integral l E T) ⟶ reduction l E T D r ⋙ totalLimit l E T D r a :=
  a.adjunction.unit

/-- The actual quotient-normalized total-limit projection.
Source: blueprint paragraph (2), pi_n
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def projection (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (a : LimitPresentation l E T D r) (n : ℕ) :
    totalLimit l E T D r a ⟶ spDerivedCompletedEvaluation l E T D n :=
  letI := a.additive
  letI := a.limits
  letI := a.colimits
  spCompletedTotalProjection l E T D n

/-- The constant-ring strict-tower open comparison, fixed as the constant-diagram mate.
Source: blueprint paragraph (2); Stacks 09BP
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def openLimit {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :=
  cbcRealizationLimitMap (openOrd l E j)

/-- Inverse evaluation transport for the recorded exact equivalence.
Source: blueprint paragraph (2), section-model evaluations
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def inverseEvaluation {A : Type a} {B : Type b} {C : Type c} [Category.{va} A]
    [Category.{vb} B] [Category.{vc} C] (e : A ≌ B)
    (F : B ⥤ C) (G : A ⥤ C) (v : e.functor ⋙ F ≅ G) : e.inverse ⋙ G ≅ F :=
  Functor.isoWhiskerLeft e.inverse v.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e.counitIso F ≪≫ Functor.leftUnitor F

/-- Identity-on-sections comparison of the two recorded exact tower evaluations.
Source: blueprint paragraph (2), simultaneous section model
(blueprint: def-sp-complete-compactification-limit-comparison). -/
structure Evaluation (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) where
  ordinary : ∀ n : ℕ, (b.realization T).functor ⋙ SpTowerShriek.ev l E T n ≅
    spCoefficientEvaluation l E T D.equivalence n
  sections : ∀ (n : ℕ) (C : spCoefficientTowers l E T) (U : T.ProEtᵒᵖ)
    (x : ((SpTowerShriek.ev l E T n).obj ((b.realization T).functor.obj C)).val.obj U),
    HEq (((ordinary n).hom.app C).val.app U x) x

/-- The ordinary tower functor induced by a fixed coefficient-module functor.
Source: blueprint paragraph (2), preservation of all quotient transitions
(blueprint: def-sp-complete-compactification-limit-comparison). -/
abbrev fixedEvaluation (T : Scheme.{u}) (n : ℕ) :=
  ((CategoryTheory.evaluation ℕᵒᵖ (scalarReductionSource l E T)).obj (op n))

/-- Evaluation of fixed-ring open extension is the exact localization of the
ordinary identity of component functors.
Source: blueprint paragraph (2), quotient projection normalization
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def fixedOpenEvaluation {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (n : ℕ) :=
  Functor.mapDerivedCategoryCompIso (fixedOpenOrd l E j) (fixedEvaluation l E Z n) ≪≫
    (Functor.mapDerivedCategoryCompIso (fixedEvaluation l E X n) (openOrd l E j)).symm

/-- Ordinary finite-level open evaluation; the comparison preserves the actual open unit.
Source: blueprint paragraph (2)
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def ordinaryOpenEvaluation (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (DX : SpCoefficientTowersAbelian l E X)
    (DZ : SpCoefficientTowersAbelian l E Z) (eX : Evaluation l E b X DX)
    (eZ : Evaluation l E b Z DZ) (n : ℕ) :
    ordinaryTowerOpen l E b o j ⋙ spCoefficientEvaluation l E Z DZ.equivalence n ≅
      spCoefficientEvaluation l E X DX.equivalence n ⋙
        sfIntrinsicExtensionByZero j (SpTowerShriek.R l E n) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (inverseEvaluation _ _ _ (eZ.ordinary n))) ≪≫
    Functor.isoWhiskerLeft _ ((o.openOp j).evaluation n) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (eX.ordinary n) _

/-- Ordinary finite-level direct-image evaluation, with unchanged sections.
Source: blueprint paragraph (2)
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def ordinaryPushEvaluation (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (DZ : SpCoefficientTowersAbelian l E Z) (DY : SpCoefficientTowersAbelian l E Y)
    (eZ : Evaluation l E b Z DZ) (eY : Evaluation l E b Y DY) (n : ℕ) :
    ordinaryTowerPush l E b o p ⋙ spCoefficientEvaluation l E Y DY.equivalence n ≅
      spCoefficientEvaluation l E Z DZ.equivalence n ⋙
        proEtaleConstantRingPushforward (SpTowerShriek.R l E n) p :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (inverseEvaluation _ _ _ (eY.ordinary n))) ≪≫
    Functor.isoWhiskerLeft _ ((o.geometry p).ordinaryPushEvaluation n) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (eZ.ordinary n) _

/-- Ordinary open/scalar comparison, fixed by its adjunction unit.
Source: blueprint paragraph (2); Stacks 03DI
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def ordinaryOpenScalar (b : SpTowerShriek.Base l E) (h : ScalarSquares l E)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (n : ℕ) :=
  asIso (PurCompactSupport.openRestrictionMap (coefficientChange l E h n) j) ≪≫
    Functor.isoWhiskerRight (finiteOpen l E b j n) (spCompletedEllRestriction l E Z n)

/-- Ordinary direct-image/scalar comparison, fixed by identity on sections.
Source: blueprint paragraph (2); Stacks 03D7
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def ordinaryPushScalar (h : ScalarSquares l E) {Z Y : Scheme.{u}} (p : Z ⟶ Y) (n : ℕ) :=
  (proEtaleRingRestrictionDirectImage p
    ((PurCompactSupport.completed l E).ring Y) ((finiteCoefficients l E n).ring Y)
    ((PurCompactSupport.completed l E).ring Z) ((finiteCoefficients l E n).ring Z)
    ((coefficientChange l E h n).map Y) ((coefficientChange l E h n).map Z)
    ((PurCompactSupport.completed l E).pull p) ((finiteCoefficients l E n).pull p)
    ((coefficientChange l E h n).square p)).symm

/-- Localize the specified ordinary open/scalar square with the standard composition
factors. This definition retains the strict transitions before passing to complexes.
Source: blueprint paragraph (2); Stacks 03DJ
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def deriveOpenScalar (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (DX : SpCoefficientTowersAbelian l E X) (DZ : SpCoefficientTowersAbelian l E Z)
    (rX : SpReductionTower l E X DX) (rZ : SpReductionTower l E Z DZ)
    (aX : LimitPresentation l E X DX rX) (aZ : LimitPresentation l E Z DZ rZ)
    (e : forgetting l E X DX ⋙ fixedOpenOrd l E j ≅
      ordinaryTowerOpen l E b o j ⋙ forgetting l E Z DZ) :
    forgetDerived l E X DX rX aX ⋙ (fixedOpenOrd l E j).mapDerivedCategory ≅
      towerOpen l E b o j DX DZ ⋙ forgetDerived l E Z DZ rZ aZ :=
  letI := DX.hasDerived
  letI := DZ.hasDerived
  letI := aX.additive
  letI := aX.limits
  letI := aX.colimits
  letI := aZ.additive
  letI := aZ.limits
  letI := aZ.colimits
  Functor.mapDerivedCategorySquareIso e

/-- The canonical localization factor for scalar forgetting on complexes.
Source: blueprint paragraph (2), direct-image unit normalization
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def forgettingFactors (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) (a : LimitPresentation l E T D r) :=
  letI := D.hasDerived
  letI := a.additive
  letI := a.limits
  letI := a.colimits
  (forgetting l E T D).mapDerivedCategoryFactors

/-- The right-derived unit of the simultaneous tower direct image, on cochain complexes.
Source: blueprint paragraph (2); Stacks 0D6E
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def towerPushUnit (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (DZ : SpCoefficientTowersAbelian l E Z) (DY : SpCoefficientTowersAbelian l E Y)
    (I : CochainComplex (spCoefficientTowers l E Z) ℤ) :=
  letI := DZ.hasDerived
  letI := DY.hasDerived
  letI := DZ.grothendieck
  (ordinaryTowerPush l E b o p).rightDerivedFunctorUnitQ I

/-- The complex-level inverse-limit normalization for the scalar/direct-image square.
It equates the two composition units, without assuming that scalar restriction preserves
K-injectives. Source: blueprint paragraph (2); Stacks 0D6E
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def IsPushScalarNormalized (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (DZ : SpCoefficientTowersAbelian l E Z) (DY : SpCoefficientTowersAbelian l E Y)
    (rZ : SpReductionTower l E Z DZ) (rY : SpReductionTower l E Y DY)
    (aZ : LimitPresentation l E Z DZ rZ) (aY : LimitPresentation l E Y DY rY)
    (d₀ : forgetting l E Z DZ ⋙ fixedPushOrd l E p ≅
      ordinaryTowerPush l E b o p ⋙ forgetting l E Y DY)
    (d : forgetDerived l E Z DZ rZ aZ ⋙ (fixedPushOrd l E p).rightDerivedFunctor ≅
      towerPush l E b o p DZ DY ⋙ forgetDerived l E Y DY rY aY) : Prop := by
  letI := aZ.additive
  letI := aY.additive
  exact ∀ I : CochainComplex (spCoefficientTowers l E Z) ℤ,
    (fixedPushOrd l E p).rightDerivedFunctorUnitQ
        (((forgetting l E Z DZ).mapHomologicalComplex (.up ℤ)).obj I) ≫
      (fixedPushOrd l E p).rightDerivedFunctor.map
        ((forgettingFactors l E Z DZ rZ aZ).inv.app I) ≫
      d.hom.app ((spTowerLocalization l E Z DZ).obj I) =
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex d₀ (.up ℤ)).hom.app I) ≫
      (forgettingFactors l E Y DY rY aY).inv.app
        (((ordinaryTowerPush l E b o p).mapHomologicalComplex (.up ℤ)).obj I) ≫
      (forgetDerived l E Y DY rY aY).map (towerPushUnit l E b o p DZ DY I)

/-- The fixed compactification composite of the separately derived ringed operations.
Source: blueprint paragraph (2), Rf_!^c
(blueprint: def-sp-complete-compactification-limit-comparison). -/
abbrev image {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  (openOrd l E c.i).mapDerivedCategory ⋙ (pushOrd l E c.g).rightDerivedFunctor

/-- The completed-coefficient strict-system comparison, prior to taking its total limit.
Source: blueprint paragraph (2), b_N = d_(jN) Rp_*(e_N)
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def scalarComposite (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (DX : SpCoefficientTowersAbelian l E X) (DZ : SpCoefficientTowersAbelian l E c.Z)
    (DY : SpCoefficientTowersAbelian l E Y)
    (rX : SpReductionTower l E X DX) (rZ : SpReductionTower l E c.Z DZ)
    (rY : SpReductionTower l E Y DY)
    (aX : LimitPresentation l E X DX rX) (aZ : LimitPresentation l E c.Z DZ rZ)
    (aY : LimitPresentation l E Y DY rY)
    (e₀ : forgetting l E X DX ⋙ fixedOpenOrd l E c.i ≅
      ordinaryTowerOpen l E b o c.i ⋙ forgetting l E c.Z DZ)
    (d : forgetDerived l E c.Z DZ rZ aZ ⋙ (fixedPushOrd l E c.g).rightDerivedFunctor ≅
      towerPush l E b o c.g DZ DY ⋙ forgetDerived l E Y DY rY aY) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (deriveOpenScalar l E b o c.i DX DZ rX rZ aX aZ e₀)
      (fixedPushOrd l E c.g).rightDerivedFunctor ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ d ≪≫
    (Functor.associator _ _ _).symm

/-- The specified canonical comparison word: compact-support image of the completion
unit, open/limit mate, direct-image/limit mate, then the limit of the strict scalar square.
This is a natural transformation on the full unbounded source category; completeness
is needed only for its invertibility.
Source: blueprint paragraph (2), normalization equality
(blueprint: def-sp-complete-compactification-limit-comparison). -/
def comparison (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (DX : SpCoefficientTowersAbelian l E X) (DZ : SpCoefficientTowersAbelian l E c.Z)
    (DY : SpCoefficientTowersAbelian l E Y)
    (rX : SpReductionTower l E X DX) (rZ : SpReductionTower l E c.Z DZ)
    (rY : SpReductionTower l E Y DY)
    (aX : LimitPresentation l E X DX rX) (aZ : LimitPresentation l E c.Z DZ rZ)
    (aY : LimitPresentation l E Y DY rY)
    (e₀ : forgetting l E X DX ⋙ fixedOpenOrd l E c.i ≅
      ordinaryTowerOpen l E b o c.i ⋙ forgetting l E c.Z DZ)
    (d : forgetDerived l E c.Z DZ rZ aZ ⋙ (fixedPushOrd l E c.g).rightDerivedFunctor ≅
      towerPush l E b o c.g DZ DY ⋙ forgetDerived l E Y DY rY aY) :
    image l E c ⟶ reduction l E X DX rX ⋙
      (towerOpen l E b o c.i DX DZ ⋙ towerPush l E b o c.g DZ DY) ⋙
        totalLimit l E Y DY rY aY :=
  Functor.whiskerRight (completionUnit l E X DX rX aX) (image l E c) ≫
    Functor.whiskerLeft (reduction l E X DX rX)
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Functor.whiskerLeft (forgetDerived l E X DX rX aX)
          (openLimit l E c.i)) (pushOrd l E c.g).rightDerivedFunctor ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ ((Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft _ (pushLimit l E c.g).hom ≫
          (Functor.associator _ _ _).inv) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (scalarComposite l E b o c DX DZ DY rX rZ rY aX aZ aY e₀ d).hom
          (coefficientConstantTowerLimit l E Y) ≫
        (Functor.associator _ _ _).hom)

end AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
