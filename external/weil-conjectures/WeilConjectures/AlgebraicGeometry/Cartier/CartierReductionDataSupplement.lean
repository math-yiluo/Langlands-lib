/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CartierPoleBoundary
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClassDefsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.Algebra.Homology.DivisibleReduction.DivisibleExtensionDerivedReductionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonPullbackSections
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonExt
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import WeilConjectures.AlgebraicGeometry.ComparisonForgetScalars
import WeilConjectures.AlgebraicGeometry.RawModuleScalarComparison.RawModuleScalarDerivedPullbackIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.ScalarUnitExtComparison
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension
import WeilConjectures.AlgebraicGeometry.ScalarUnitExt
import WeilConjectures.AlgebraicGeometry.ExactFunctorDerivedUnit
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.Derived.DerivedScalarExtUnit
import WeilConjectures.AlgebraicGeometry.EtaleSupportedIntegralDerivedUnit
import WeilConjectures.AlgebraicGeometry.ResidueQuotientDerivedUnit
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Data.ZMod.Basic
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
import WeilConjectures.Algebra.Homology.DivisibleReduction.DivisibleExtensionDerivedReductionSupplement
import WeilConjectures.Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import WeilConjectures.SixFunctors.BaseChange.DerivedForget
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.AlgebraicGeometry.SupportedKummerScalarSource
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerScalarSupplement
import WeilConjectures.AlgebraicGeometry.SupportedKummerScalarMaps
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
import WeilConjectures.AlgebraicGeometry.SupportedKummerScalarDerived
import WeilConjectures.CategoryTheory.FlatScalarUnit
import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import WeilConjectures.AlgebraicGeometry.FiniteOrdinaryScalarUnit
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.SixFunctors.Finite.Stalk
import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.AlgebraicGeometry.ScalarUniversalDerivedUnit
import WeilConjectures.AlgebraicGeometry.SupportedIntegralResidueSequence
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.SixFunctors.Finite.Exact
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.CartierComplementFrame
import WeilConjectures.AlgebraicGeometry.Modules.SectionAvoidance
import WeilConjectures.AlgebraicGeometry.InternalHomRestrictScheme
import WeilConjectures.AlgebraicGeometry.OpenClosedIntegralSections
import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyComparison
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerCoefficients
import WeilConjectures.CategoryTheory.Sites.RelativeTorsorExtension
import WeilConjectures.CategoryTheory.Sites.TorsorExtensionPresentation
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.CategoryTheory.Sites.EtaleTorsorExtensionPresentationExists
import WeilConjectures.CategoryTheory.Sites.ExtensionPresentationShortExact
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import WeilConjectures.AlgebraicGeometry.ProEtaleUnitsComparison
import WeilConjectures.Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.AlgebraicGeometry.ProEtaleUnitsSheaf
import WeilConjectures.AlgebraicGeometry.ProEtaleStructureSheaf
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.Algebra.Category.Grp.Ulift
import WeilConjectures.Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
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
public import WeilConjectures.AlgebraicGeometry.CartierReductionData

/-!
# Cartier boundary and normalized reduction constructions

Source: blueprint main-20261015, sk-lem-geo-cartier.proof.md, (G1), derived reduction,
and opening comparison paragraphs (blueprint: lem-sp-cartier-reduction-site-comparison).

The derived scalar units below are expressed by their Hom adjunction against every
unbounded complex. This is an equivalent, model-independent specification of derived
extension of scalars at the supported constant and at G_m. In particular the equality
of reduced maps is an equality in module Ext, not a test on the global section one.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u uC uB vC vB wC wB wE
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

end AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.cartierEtaleAbSheafify
  WeilConjectures.sfAbSheafify AlgebraicGeometry.cartierEtaleModuleSheafify
  AlgebraicGeometry.cartierProModuleSheafify

attribute [local instance] AlgebraicGeometry.cartierEtaleAbHasExt
  AlgebraicGeometry.ProEtale.geoCartierIntegralExt AlgebraicGeometry.Etale.hasExt_sheaf_moduleCat
  AlgebraicGeometry.ProEtale.geoCartierModuleExt

namespace AlgebraicGeometry.Etale

private theorem supported_one_restrict {D Z : Scheme.{u}} (i : D ⟶ Z)
    (U : Z.Etaleᵒᵖ) :
    ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D)).obj.map
      ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Z).from U.unop).op
      ((supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 Z)))
        (supportedIntegralOne Z)) =
    (supportedIntegralUnit i).hom.app U ((toSheafify Z.smallEtaleTopology
      ((Functor.const Z.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U ⟨1⟩) := by
  let v := ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Z).from U.unop).op
  have hq := ConcreteCategory.congr_hom ((supportedIntegralUnit i).hom.naturality v)
    (supportedIntegralOne Z)
  have h1 := ConcreteCategory.congr_hom
    ((toSheafify Z.smallEtaleTopology
      ((Functor.const Z.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality v)
    (ULift.up 1)
  simp only [ConcreteCategory.comp_apply, Functor.const_obj_map] at hq h1
  exact hq.symm.trans (congrArg ((supportedIntegralUnit i).hom.app U) h1.symm)

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] comparisonUpperStar Etale.cartierPoleBoundary
attribute [local instance 0] IsGroupoid.all_isIso isIso_of_isDiscrete
  HasZeroObject.zero_to_zero_isIso to_initial_isIso terminal_isIso_from initial_isIso_to

/-- Scalar forgetting is exact on the original pro-etale site.
Source: Stacks 03D7 (blueprint: lem-sp-cartier-reduction-site-comparison).
Proof: kernels are sectionwise, and cokernels are the sheafifications of the same
abelian presheaf cokernels. The scalar action descends uniquely to these cokernels. -/
theorem cartierForget_exact (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :
    PreservesFiniteLimits (cartierForget A Z) ∧
      PreservesFiniteColimits (cartierForget A Z) := by
  constructor
  · have : PreservesFiniteLimits (cartierForget A Z ⋙ sheafToPresheaf _ _) :=
      inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj
          (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})))
    exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  · have := (Sheaf.forget₂CoinduceAdj (Scheme.ProEt.topology Z) A).isLeftAdjoint
    infer_instance

/-- Exactness on finite limits. Source: Stacks 03D7
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
instance cartierForgetLimits (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :
    PreservesFiniteLimits (cartierForget A Z) := (cartierForget_exact A Z).1

/-- Exactness on finite colimits. Source: Stacks 03D7
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
instance cartierForgetColimits (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :
    PreservesFiniteColimits (cartierForget A Z) := (cartierForget_exact A Z).2

/-- Additivity on sections. Source: Stacks 03D7
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
instance cartierForgetAdditive (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :
    (cartierForget A Z).Additive where

attribute [local irreducible] cartierIntegralConstantComparisonIso

attribute [local irreducible] cartierIntegralSourceComparison cartierIntegralSourceIso
  cartierUnitsComparison

private theorem unitsComparison_isIso (Z : Scheme.{u}) : IsIso (cartierUnitsComparison Z) := by
  unfold cartierUnitsComparison
  rw [Adjunction.homEquiv_counit]
  let e : Z.gmSheaf ≅
      (comparisonLowerStar AddCommGrpCat.{u + 1} Z).obj (Scheme.proEtaleUnitsSheaf Z) :=
    ⟨⟨𝟙 _⟩, ⟨𝟙 _⟩, by ext U x; rfl, by ext U x; rfl⟩
  have : IsIso e.hom := e.isIso_hom
  have := proEtaleUnitsCounit_isIso Z
  infer_instance

attribute [local irreducible] cartierRootsComparison cartierRootsIso

attribute [local irreducible] cartierProRootMap cartierProIntegralGenerator

attribute [local irreducible] cartierProBoundary cartierEtaleKummerUnit cartierProKummerUnit

attribute [local irreducible] CartierEtaleReductionSpec CartierProReductionSpec

private theorem cartierSourceComparison_isIso (A : Type (u + 1)) [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    IsIso (geoCartierSourceComparison A i) := by
  have := isIso_lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)
  unfold geoCartierSourceComparison
  infer_instance

private theorem cartierProIntegralGenerator_ext_bijective
    (A : Type (u + 1)) [CommRing A] [Finite A] (n : ℕ) (hn : 0 < n)
    (hA : (n : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    Function.Bijective (fun c : GeoCartierClass A n hA i ↦
      (Ext.mk₀.{u + 1} (cartierProIntegralGenerator A i)).comp
        (c.mapExactFunctor (cartierForget A Z)) (zero_add 2)) := by
  have hsource := Etale.supported_integral_derived_unit Z n hn A hA i
  have hU := scalar_unit_ext_bijective
    (Etale.RawModuleScalarComparison.forget A Z)
    (Q := Scheme.finiteEtaleTateLine Z n A hA)
    (Etale.supportedIntegralGenerator A i) hsource 2
  have : IsIso (geoCartierSourceComparison A i) := cartierSourceComparison_isIso A i
  have hF := comparison_mapExt_bijective (ModuleCat.{u + 1} A) Z
    ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj (Etale.ordinaryFiniteConstant A D))
    (Scheme.finiteEtaleTateLine Z n A hA) 2
  have hG := comparison_mapExt_bijective AddCommGrpCat.{u + 1} Z
    ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj (Etale.supportedIntegralConstant D))
    ((Etale.RawModuleScalarComparison.forget A Z).obj
      (Scheme.finiteEtaleTateLine Z n A hA)) 2
  have h := Ext.scalar_unit_ext_comparison_bijective
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z)
    (comparisonUpperStar AddCommGrpCat.{u + 1} Z)
    (Etale.RawModuleScalarComparison.forget A Z) (cartierForget A Z)
    (forgetComparisonIso A Z) (Etale.supportedIntegralGenerator A i)
    (cartierIntegralSourceIso i) (asIso (geoCartierSourceComparison A i)) 2 hU hF hG
  unfold cartierProIntegralGenerator cartierForgetComparison
  simpa only [forgetComparisonIso_hom, asIso_hom, cartierForget, Functor.comp_obj,
    GeoCartierClass, geoCartierLine] using h

attribute [local irreducible] cartierReducedEtale cartierReducedPro

/-- The Hom universal property of a derived scalar unit with a shifted sheaf target.
It is tested against every unbounded complex, and therefore determines the target up
to its unique unit-compatible isomorphism.
Source: Stacks 09T5, 0FND and blueprint Cartier reduction paragraphs
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
def CartierScalarUnit
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B] [HasExt.{wE} B]
    (U : C ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (F : B) (H : C) (n : ℕ) (e : Ext F (U.obj H) n) : Prop :=
  U.DerivedExtUnit F H n e

/-- The specified R-algebra structure on A, uniquely determined by its integer action.
Source: blueprint Cartier finite coefficient extension paragraph
(blueprint: lem-sp-cartier-reduction-site-comparison). -/
def cartierResidueAlgebra (ℓ r : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : ((ℓ ^ r : ℕ) : A) = 0) : cartierResidueRing.{u} ℓ r →+* A :=
  (Scheme.finiteEtaleTwistScalar (ℓ ^ r) A hA).comp ULift.ringEquiv.toRingHom

attribute [local irreducible] cartierResidueReducedPro

end AlgebraicGeometry.ProEtale
