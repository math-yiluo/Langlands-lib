/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
public import WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
public import WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen
public import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
public import WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
public import WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
public import WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.AlgebraicGeometry.ProperMorphismFpqcDescent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
public import WeilConjectures.AlgebraicGeometry.ProperSupportCompositeRange
public import WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
public import WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
public import WeilConjectures.AlgebraicGeometry.ProperSupportExchangeRange
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility
public import WeilConjectures.SecSmoothPurity.ProperSupportPullbackSectionMap
public import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalk
public import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.OpenClosed.Complex
public import WeilConjectures.AlgebraicGeometry.ProperGeometricPointExchange
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.ProperStrictLocalFibreSections
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
public import WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
public import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
public import WeilConjectures.AlgebraicGeometry.QcqsGeometricExchangeFactorization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
public import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
public import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
public import WeilConjectures.RingTheory.StrictHenselizationTriples
public import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
public import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
public import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
public import WeilConjectures.AlgebraicGeometry.EtaleUnitSectionRestriction
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
public import WeilConjectures.AlgebraicGeometry.SmallStrictLocalSectionMaps
public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointCanonicalGerm
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalkCore
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.SixFunctors.OpenClosed.Exact
public import WeilConjectures.SixFunctors.BaseChange.Pasting
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
public import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.GeometricRingTransport
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenAdjunctionNormalization
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenPastingSupplement
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenBaseChange
import WeilConjectures.AlgebraicGeometry.OpenExtendedInjectiveProperAcyclic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-!
# Unbounded proper/open interchange and its canonical normalizations

Source: Stacks Project, More on Étale Cohomology, Tags 0F7B (case (b)), 0F7C, 0F7D
and 0F7F (blueprint: lem-amb-unbounded-proper-open-interchange).

The sheaf isomorphism is specified by equality of its two maps into the common direct
image. This is precisely equality of the proper-support subsheaves, and fixes the map.
The derived isomorphism is specified on every K-injective representative and every
K-injective resolution of its open extension. All composition equations include the
canonical composition isomorphisms. No boundedness of the input is imposed.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance 2000] Abelian.toPreadditive

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem exists_sheafComparison (A : Type (u + 1)) [CommRing A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : CommSq k r p i) :
    ∃ θ : (r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅
        (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A],
      ∀ F, θ.hom.app F ≫
          (p)_*[ModuleCat.{u + 1} A].map
            ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} A) k p).hom.app F =
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
            ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq.w).hom.app F := by
  classical
  obtain ⟨L, ι, hι, hp, ho, c, e, hc, he, hce⟩ := properSupportSheafComposition A
  have hproper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] : IsIso (ι f) := by
    have (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) : IsIso ((ι f).app F) :=
      hp X Y f F
    exact NatIso.isIso_of_isIso_app _
  have := hproper r
  have := hproper p
  obtain ⟨ok, hk⟩ := ho U V k
  obtain ⟨oi, hi⟩ := ho W Z i
  let er : L r ≅ (r)_*[ModuleCat.{u + 1} A] := asIso (ι r)
  let ep : L p ≅ (p)_*[ModuleCat.{u + 1} A] := asIso (ι p)
  have hcomp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
      (h : X ⟶ Z) [IsSeparated h] [LocallyOfFiniteType h] (hh : h = f ≫ g) :
      ∃ co : L f ⋙ L g ≅ L h, ∀ F,
        co.hom.app F ≫ (ι h).app F = (ι g).app ((L f).obj F) ≫
          (g)_*[ModuleCat.{u + 1} A].map ((ι f).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} A) f g h hh).hom.app F := by
    subst h
    exact ⟨c X Y Z f g, hc X Y Z f g⟩
  obtain ⟨co, hco⟩ := hcomp r i (k ≫ p) sq.w
  let t : (r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅ L (k ≫ p) :=
    Functor.isoWhiskerRight er.symm _ ≪≫ Functor.isoWhiskerLeft _ oi ≪≫ co
  let b : (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A] ≅ L (k ≫ p) :=
    Functor.isoWhiskerLeft _ ep.symm ≪≫ Functor.isoWhiskerRight ok _ ≪≫ c U V Z k p
  refine ⟨t ≪≫ b.symm, fun F => ?_⟩
  have ht : t.hom.app F ≫ (ι (k ≫ p)).app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
          ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq.w).hom.app F := by
    dsimp only [t, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Iso.symm_hom]
    simp only [Category.assoc]
    rw [hco]
    simp only [← Category.assoc, ← NatTrans.comp_app, hi]
    rw [(openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).naturality]
    simp only [Category.assoc]
    change _ ≫ (i)_*[ModuleCat.{u + 1} A].map (er.inv.app F) ≫
      (i)_*[ModuleCat.{u + 1} A].map (er.hom.app F) ≫ _ = _
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hb : b.hom.app F ≫ (ι (k ≫ p)).app F =
      (p)_*[ModuleCat.{u + 1} A].map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) k p).hom.app F := by
    dsimp only [b, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Iso.symm_hom]
    simp only [Category.assoc]
    rw [hc, reassoc_of% (ι p).naturality (ok.hom.app F)]
    change ep.inv.app _ ≫ ep.hom.app _ ≫ _ = _
    rw [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, ← NatTrans.comp_app, hk]
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom]
  rw [← hb, Category.assoc, Iso.inv_hom_id_app_assoc]
  exact ht

private theorem exists_termwise_injective_resolution
    {C : Type v} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    (J : CochainComplex C ℤ) :
    ∃ J' : CochainComplex C ℤ, J'.IsKInjective ∧
      (∀ n, Injective (J'.X n)) ∧ ∃ a : J ⟶ J', QuasiIso a := by
  refine ⟨(CochainComplex.kInjectiveResolutionFunctor.{w} C).obj J,
    inferInstance, fun n => inferInstance,
    (CochainComplex.toKInjectiveResolution.{w} C).app J,
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{w} C J).2⟩

private theorem derivedUnit_of_termwise_injective_resolution
    {C₀ C₁ C₂ : Type v} [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂]
    [Abelian C₀] [Abelian C₁] [Abelian C₂]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [IsGrothendieckAbelian.{w} C₀] [IsGrothendieckAbelian.{w} C₁]
    [HasInjectiveResolutions C₁]
    [Abelian.HasKInjectiveResolutions C₀] [Abelian.HasKInjectiveResolutions C₁]
    (P : C₁ ⥤ C₂) (K : C₀ ⥤ C₁) [P.Additive] [K.Additive]
    [PreservesFiniteLimits P]
    (hacyclic : ∀ M : CochainComplex C₁ ℤ, M.Acyclic →
      (∀ n, P.rightAcyclic (M.X n)) → ((P.mapHomologicalComplex (.up ℤ)).obj M).Acyclic)
    (hterm : ∀ (F : C₀) [Injective F], P.rightAcyclic (K.obj F))
    (J : CochainComplex C₀ ℤ) [J.IsKInjective] :
    IsIso (P.rightDerivedFunctorUnit.app
      ((K.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj J))) := by
  obtain ⟨J', hJ', hterms, a, hqa⟩ := exists_termwise_injective_resolution J
  have := hJ'
  have (n : ℤ) := hterms n
  have := hqa
  have ha : IsIso ((HomotopyCategory.quotient _ _).map a) := by
    have h := (CochainComplex.IsKInjective.quasiIso_iff a).mp inferInstance
    rwa [← HomotopyCategory.inverseImage_quotient_isomorphisms,
      MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff] at h
  have hJ' : IsIso (P.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj
        ((K.mapHomologicalComplex (.up ℤ)).obj J'))) :=
    P.isIso_rightDerivedFunctorUnit_app_of_rightAcyclic_of_map_acyclic
      hacyclic _ (fun n => hterm (J'.X n))
  exact (NatTrans.isIso_app_iff_of_iso P.rightDerivedFunctorUnit
    ((K.mapHomotopyCategory (.up ℤ)).mapIso
      (asIso ((HomotopyCategory.quotient _ _).map a)))).2 hJ'

private theorem openExtension_derivedUnit_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : CommSq k r p i)
    (J : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [J.IsKInjective] :
    IsIso (((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorUnit.app
      (((k)_!open[ModuleCat.{u + 1} A].mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj J))) := by
  let P := (p)_*[ModuleCat.{u + 1} A]
  let K := (k)_!open[ModuleCat.{u + 1} A]
  have hacyclic (M : CochainComplex (Sheaf V.smallEtaleTopology
      (ModuleCat.{u + 1} A)) ℤ) (hM : M.Acyclic)
      (hM' : ∀ n, P.rightAcyclic (M.X n)) :
      ((P.mapHomologicalComplex (.up ℤ)).obj M).Acyclic := by
    choose d hd using exists_isZero_upperStar_rightDerived_lowerStar_of_isProper A
      (isAddTorsion_of_finite : IsAddTorsion A) p
    exact hM.map_of_rightAcyclic_of_forall_isZero P
      (fun z => (Z.algClosurePoint z)^*[ModuleCat.{u + 1} A])
      (isZero_of_forall_isZero_upperStar_algClosurePoint A) d hd hM'
  have hterm (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) [Injective F] :
      P.rightAcyclic (K.obj F) := by
    intro q
    exact (isZero_higherDirectImage_openImmersionLowerShriek_injective A
      k i r p sq.w F (q + 1) (by omega)).of_iso
        (P.homologyRightDerivedFunctorPlusObjSingleFunctorIso (K.obj F) (q + 1)).symm
  exact derivedUnit_of_termwise_injective_resolution
    (C₀ := Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (C₁ := Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
    (C₂ := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) P K hacyclic hterm J

private theorem comparison_representative
    {C₀ C₁ C₂ C₃ : Type v}
    [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    [Abelian.HasKInjectiveResolutions C₀] [Abelian.HasKInjectiveResolutions C₁]
    (R : C₀ ⥤ C₂) (P : C₁ ⥤ C₃) (K : C₀ ⥤ C₁) (E : C₂ ⥤ C₃)
    [R.Additive] [P.Additive] [K.Additive] [E.Additive]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (θ : R ⋙ E ≅ K ⋙ P)
    (Γ : R.rightDerivedFunctor ⋙ E.mapDerivedCategory ≅
      K.mapDerivedCategory ⋙ P.rightDerivedFunctor)
    (J : CochainComplex C₀ ℤ) [J.IsKInjective]
    (I : CochainComplex C₁ ℤ) [I.IsKInjective]
    (ρ : (K.mapHomologicalComplex (.up ℤ)).obj J ⟶ I) [QuasiIso ρ]
    (h' :
      E.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up
        ℤ)).obj J)) ≫
          Γ.hom.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj J)) =
        E.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj J)) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory θ.hom (.up ℤ)).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj J)) ≫
          P.rightDerivedFunctorUnit.app ((K.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ (.up ℤ)).obj J)) ≫
          P.rightDerivedFunctor.map (K.mapDerivedCategoryFactorsh.inv.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj J))) :
        E.mapDerivedCategory.map
            ((R).rightDerivedFunctorObjQIso J).hom ≫
          (E).mapDerivedCategoryFactors.hom.app
            ((R.mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app J) ≫
          DerivedCategory.Q.map
            ((P.mapHomologicalComplex (.up ℤ)).map ρ) =
        Γ.hom.app (DerivedCategory.Q.obj J) ≫
          P.rightDerivedFunctor.map
            ((K).mapDerivedCategoryFactors.hom.app J ≫
              DerivedCategory.Q.map ρ) ≫
          ((P).rightDerivedFunctorObjQIso I).hom := by
  let qJ := (HomotopyCategory.quotient _ (.up ℤ)).obj J
  have hK : K.mapDerivedCategoryFactorsh.inv.app qJ ≫
      K.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C₀).hom.app J) ≫
        K.mapDerivedCategoryFactors.hom.app J =
      (DerivedCategory.quotientCompQhIso C₁).hom.app
        ((K.mapHomologicalComplex (.up ℤ)).obj J) := by
    rw [← cancel_epi (K.mapDerivedCategoryFactorsh.hom.app qJ),
      Iso.hom_inv_id_app_assoc, K.mapDerivedCategoryFactorsh_hom_app]
    simp [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
  have hE : E.mapDerivedCategory.map
        ((DerivedCategory.quotientCompQhIso C₂).inv.app
          ((R.mapHomologicalComplex (.up ℤ)).obj J)) ≫
      E.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj qJ) =
      E.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj J) ≫
        (DerivedCategory.quotientCompQhIso C₃).inv.app
          ((E.mapHomologicalComplex (.up ℤ)).obj
            ((R.mapHomologicalComplex (.up ℤ)).obj J)) := by
    change E.mapDerivedCategory.map _ ≫ E.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ _).obj
        ((R.mapHomologicalComplex (.up ℤ)).obj J)) = _
    rw [E.mapDerivedCategoryFactorsh_hom_app]
    simp [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
      ← Functor.map_comp_assoc]
  have hn := Γ.hom.naturality ((DerivedCategory.quotientCompQhIso C₀).hom.app J)
  have ht := (DerivedCategory.quotientCompQhIso C₃).inv.naturality
    ((NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app J)
  have hu : E.mapDerivedCategory.map (R.rightDerivedFunctorUnitQ J) ≫
      Γ.hom.app (DerivedCategory.Q.obj J) ≫
        P.rightDerivedFunctor.map (K.mapDerivedCategoryFactors.hom.app J) =
      E.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj J) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app J) ≫
          P.rightDerivedFunctorUnitQ ((K.mapHomologicalComplex (.up ℤ)).obj J) := by
    simp only [Functor.comp_map] at hn ht
    simp only [Functor.rightDerivedFunctorUnitQ, Functor.map_comp, Category.assoc]
    rw [reassoc_of% hn, reassoc_of% h']
    simp only [← P.rightDerivedFunctor.map_comp]
    rw [hK]
    dsimp only [qJ] at hE
    rw [reassoc_of% hE]
    erw [← reassoc_of% ht]
    rfl
  rw [R.rightDerivedFunctorUnitQ_eq] at hu
  have hρ := P.rightDerivedFunctorUnitQ_naturality ρ
  rw [P.rightDerivedFunctorUnitQ_eq] at hρ
  rw [← cancel_epi (E.mapDerivedCategory.map (R.rightDerivedFunctorObjQIso J).inv),
    ← cancel_mono (P.rightDerivedFunctorObjQIso I).inv]
  simp only [← E.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  rw [hρ, ← reassoc_of% hu]
  simp only [Functor.map_comp]

private structure NormalizedDerivedComparison
    {C₀ C₁ C₂ C₃ : Type v}
    [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    [Abelian.HasKInjectiveResolutions C₀] [Abelian.HasKInjectiveResolutions C₁]
    (R : C₀ ⥤ C₂) (P : C₁ ⥤ C₃) (K : C₀ ⥤ C₁) (E : C₂ ⥤ C₃)
    [R.Additive] [P.Additive] [K.Additive] [E.Additive]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (θ : R ⋙ E ≅ K ⋙ P) where
  comparison : R.rightDerivedFunctor ⋙ E.mapDerivedCategory ≅
        K.mapDerivedCategory ⋙ P.rightDerivedFunctor
  unit_normalization : (∀ X : HomotopyCategory C₀ (.up ℤ),
      E.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app X) ≫
          comparison.hom.app (DerivedCategory.Qh.obj X) =
        E.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj X) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory θ.hom (.up ℤ)).app X) ≫
          P.rightDerivedFunctorUnit.app ((K.mapHomotopyCategory (.up ℤ)).obj X) ≫
          P.rightDerivedFunctor.map (K.mapDerivedCategoryFactorsh.inv.app X))
  representative_normalization : ∀ (J : CochainComplex C₀ ℤ)
        [J.IsKInjective]
        (I : CochainComplex C₁ ℤ)
        [I.IsKInjective]
        (ρ : (K.mapHomologicalComplex (.up ℤ)).obj J ⟶ I)
        [QuasiIso ρ],
        E.mapDerivedCategory.map
            ((R).rightDerivedFunctorObjQIso J).hom ≫
          (E).mapDerivedCategoryFactors.hom.app
            ((R.mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app J) ≫
          DerivedCategory.Q.map
            ((P.mapHomologicalComplex (.up ℤ)).map ρ) =
        comparison.hom.app (DerivedCategory.Q.obj J) ≫
          P.rightDerivedFunctor.map
            ((K).mapDerivedCategoryFactors.hom.app J ≫
              DerivedCategory.Q.map ρ) ≫
          ((P).rightDerivedFunctorObjQIso I).hom

@[irreducible]
private noncomputable def constructedDerivedComparison
    {C₀ C₁ C₂ C₃ : Type v}
    [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    [Abelian.HasKInjectiveResolutions C₀] [Abelian.HasKInjectiveResolutions C₁]
    (R : C₀ ⥤ C₂) (P : C₁ ⥤ C₃) (K : C₀ ⥤ C₁) (E : C₂ ⥤ C₃)
    [R.Additive] [P.Additive] [K.Additive] [E.Additive]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (hP : ∀ (J : CochainComplex C₀ ℤ) [J.IsKInjective],
      IsIso (P.rightDerivedFunctorUnit.app ((K.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj J))))
    (θ : R ⋙ E ≅
      K ⋙ P) :
    NormalizedDerivedComparison R P K E θ := by
  let α := Functor.rightDerivedFunctorCompMapDerivedCategoryUnit R E
  let β := Functor.mapDerivedCategoryCompRightDerivedFunctorUnit K P
  have hβ : (K.mapDerivedCategory ⋙ P.rightDerivedFunctor).IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso _ (.up ℤ)) := by
    refine (HomotopyCategory.KInjectives.localizerMorphism_derives
      ((K ⋙ P).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).isRightDerivedFunctor_of_isIso
      β (fun X => ?_)
    obtain ⟨J, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X
    change IsIso (β.app ((HomotopyCategory.quotient _ _).obj J))
    have hPJ : IsIso (P.rightDerivedFunctorUnit.app
        ((K.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj J))) :=
      hP J
    dsimp only [β]
    rw [Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app]
    infer_instance
  let θh : (R ⋙ E).mapHomotopyCategory (.up ℤ) ≅
      (K ⋙ P).mapHomotopyCategory (.up ℤ) :=
    { hom := NatTrans.mapHomotopyCategory θ.hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory θ.inv (.up ℤ)
      hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp, θ.hom_inv_id,
        NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp, θ.inv_hom_id,
        NatTrans.mapHomotopyCategory_id] }
  let Γ := Functor.rightDerivedNatIso
    (R.rightDerivedFunctor ⋙ E.mapDerivedCategory)
    (K.mapDerivedCategory ⋙ P.rightDerivedFunctor) α β
    (HomotopyCategory.quasiIso _ (.up ℤ))
    (Functor.isoWhiskerRight θh DerivedCategory.Qh)
  have hn (X : HomotopyCategory C₀ (.up ℤ)) :
      E.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app X) ≫
          Γ.hom.app (DerivedCategory.Qh.obj X) =
        E.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj X) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory θ.hom (.up ℤ)).app X) ≫
          P.rightDerivedFunctorUnit.app ((K.mapHomotopyCategory (.up ℤ)).obj X) ≫
          P.rightDerivedFunctor.map (K.mapDerivedCategoryFactorsh.inv.app X) := by
    obtain ⟨J, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    have h := Functor.rightDerivedNatTrans_app
      (R.rightDerivedFunctor ⋙ E.mapDerivedCategory)
      (K.mapDerivedCategory ⋙ P.rightDerivedFunctor) α β
      (HomotopyCategory.quasiIso _ (.up ℤ))
      (Functor.whiskerRight (NatTrans.mapHomotopyCategory θ.hom (.up ℤ)) DerivedCategory.Qh)
      ((HomotopyCategory.quotient _ _).obj J)
    change α.app _ ≫ Γ.hom.app _ = _ at h
    let qJ := (HomotopyCategory.quotient _ (.up ℤ)).obj J
    have h' :
        E.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app qJ) ≫
            Γ.hom.app (DerivedCategory.Qh.obj qJ) =
          E.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj qJ) ≫
            DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory θ.hom (.up ℤ)).app qJ) ≫
            P.rightDerivedFunctorUnit.app ((K.mapHomotopyCategory (.up ℤ)).obj qJ) ≫
            P.rightDerivedFunctor.map (K.mapDerivedCategoryFactorsh.inv.app qJ) := by
      have hα := Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app' R E qJ
      have hβ : β.app qJ =
          P.rightDerivedFunctorUnit.app ((K.mapHomotopyCategory (.up ℤ)).obj qJ) ≫
            P.rightDerivedFunctor.map (K.mapDerivedCategoryFactorsh.inv.app qJ) := by
        have hc : (Functor.mapHomotopyCategoryCompIso
            (Iso.refl (K ⋙ P)) (.up ℤ)).inv.app qJ = 𝟙 _ := by
          change (HomotopyCategory.quotient _ _).map (𝟙 _) = 𝟙 _
          exact CategoryTheory.Functor.map_id _ _
        dsimp only [β]
        rw [Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app K P,
          hc, CategoryTheory.Functor.map_id, Category.id_comp]
      change α.app qJ ≫ Γ.hom.app (DerivedCategory.Qh.obj qJ) =
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory θ.hom (.up ℤ)).app qJ) ≫
          β.app qJ at h
      conv_rhs at h => rw [hβ]
      calc
        _ = E.mapDerivedCategoryFactorsh.hom.app
            ((R.mapHomotopyCategory (.up ℤ)).obj qJ) ≫
            α.app qJ ≫ Γ.hom.app (DerivedCategory.Qh.obj qJ) := by
          symm
          rw [hα]
          simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
        _ = _ := by
          simpa only [Category.assoc] using
            congrArg (fun f => E.mapDerivedCategoryFactorsh.hom.app
              ((R.mapHomotopyCategory (.up ℤ)).obj qJ) ≫ f) h
    exact h'
  refine ⟨Γ, hn, fun J _ I _ ρ _ => ?_⟩
  exact comparison_representative R P K E θ Γ J I ρ (hn _)

set_option linter.unusedVariables false in
/-- Unbounded proper/open interchange, including its representative, adjunction, pasting,
identity and arbitrary base-change normalizations.
Source: Stacks Project, Tags 0F7B, 0F7C, 0F7D and 0F7F
(blueprint: lem-amb-unbounded-proper-open-interchange).

Proof:

1. Construct the normalized sheaf comparison from properSupportSheafComposition: the two paths
through the square identify r_* followed by i_! and k_! followed by p_* with the same
proper-support functor for k≫p=r≫i. Use the proper identifications and the open identifications,
and cancel the common composition isomorphism to obtain exactly the stated normalization into the
common direct image. This is exists_sheafComparison in Lean.
Uses: lem-cbc-proper-support-sheaf-composition, def-weil-proper-morphism, def-weil-open-immersion,
def-weil-finite-type-morphism.

2. For P=p_* and K=k_!, prove the derived unit on KJ is invertible for every K-injective J.
Resolve J by a K-injective complex Jprime whose terms are injective. The open-extended-injective
proper-acyclicity theorem says every term of KJprime is P-acyclic. For an exact complex of
P-acyclic objects use the adopted-source pointwise bound
exists_isZero_upperStar_rightDerived_lowerStar_of_isProper, the joint conservativity
isZero_of_forall_isZero_upperStar_algClosurePoint, and
HomologicalComplex.Acyclic.map_of_rightAcyclic_of_forall_isZero. Unlike the previous global-bound
route, the bound may depend on the geometric point. The right-acyclic complex API makes the
canonical unit invertible on KJprime. The resolution J→Jprime is a homotopy equivalence because
both are K-injective, so naturality transports invertibility to KJ. This is
openExtension_derivedUnit_isIso.
Uses: lem-cbc-open-extended-injective-proper-acyclic, lem-pur-kinjective-degreewise-existence,
lem-kun-pointwise-finite-cd-exact-complex, lem-weil-pbc-kinjective-hom-derived,
lem-weil-pbc-module-sheaves-grothendieck-abelian.

3. Work first with four abstract abelian categories. The canonical unit alpha for RR⋙DE is
right-derived because E is exact. The unit beta for DK⋙RP is right-derived by the K-injective
derivability structure: beta is invertible on K-injectives by the preceding step. Apply the
universal-property rightDerivedNatIso to the termwise descent of theta. Its factorization
equation, together with the exact-functor factorsh comparison, gives the unit normalization on
every homotopy object. The private NormalizedDerivedComparison record retains the constructed
isomorphism and both proved normalizations. Its irreducible constructor constructedDerivedComparison
builds the isomorphism directly, and its fields provide the normalization API.
Uses: lem-weil-pbc-extension-by-zero-exact, lem-weil-pbc-kinjective-total-derived,
lem-weil-pbc-localization-universal-property.

4. Prove comparison_representative abstractly. Transport the unit normalization along
quotientCompQhIso to the complex quotient Q, using the exact-functor factors. Apply naturality of
the derived unit to any quasi-isomorphism rho:KJ→I with I K-injective. The
rightDerivedFunctorObjQIso identifications on J and I turn the resulting equality into the
representative formula of the statement. This works for every rho and J, not just the chosen
resolutions. Apply the abstract construction to every geometric square.
Uses: lem-weil-pbc-kinjective-total-derived, lem-weil-pbc-extension-by-zero-exact.

5. Apply the independent adjunction-normalization lemma, the independent normalized
pasting-and-identities lemma, and the independent arbitrary base-change lemma to these same global
families theta and Gamma. Their hypotheses are respectively the proved support normalization,
representative normalization and homotopy-unit normalization. Assemble the eight clauses without
changing any target signature.
Uses: lem-amb-unbounded-proper-open-adjunction-normalization,
lem-amb-unbounded-proper-open-pasting, lem-amb-unbounded-proper-open-base-change.
-/
theorem unboundedProperOpenInterchange (A : Type (u + 1)) [CommRing A] [Finite A] :
    ∃ (θ : ∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i),
        (r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅
          (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A])
      (Γ : ∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i),
        R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i)_!open[ModuleCat.{u + 1} A]) ≅
          D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A])),
      (∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i)
        (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (θ k r p i sq).hom.app F ≫
            (p)_*[ModuleCat.{u + 1} A].map
              ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) k p).hom.app F =
          (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
              ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq.w).hom.app F) ∧
      (∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i)
        (J : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [J.IsKInjective]
        (I : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [I.IsKInjective]
        (ρ : ((k)_!open[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J ⟶ I)
        [QuasiIso ρ],
        D((i)_!open[ModuleCat.{u + 1} A]).map
            (((r)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso J).hom ≫
          ((i)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app
            (((r)_*[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (θ k r p i sq).hom (.up ℤ)).app J) ≫
          DerivedCategory.Q.map
            (((p)_*[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).map ρ) =
        (Γ k r p i sq).hom.app (DerivedCategory.Q.obj J) ≫
          R((p)_*[ModuleCat.{u + 1} A]).map
            (((k)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app J ≫
              DerivedCategory.Q.map ρ) ≫
          (((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso I).hom) ∧
      (∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : IsPullback k r p i),
        ∃ lam : D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]) ⋙
            D((i)^*[ModuleCat.{u + 1} A]) ≅ R((r)_*[ModuleCat.{u + 1} A]),
          (∀ K : DerivedCategoryModule A U,
            lam.hom.app K =
              (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
                  (D((k)_!open[ModuleCat.{u + 1} A]).obj K) ≫
                R((r)_*[ModuleCat.{u + 1} A]).map
                  (inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction
                    (ModuleCat.{u + 1} A) k).unit.app K))) ∧
          ∀ K : DerivedCategoryModule A U,
            (Γ k r p i sq.toCommSq).hom.app K =
              D((i)_!open[ModuleCat.{u + 1} A]).map (lam.inv.app K) ≫
                (derivedOpenImmersionLowerShriekUpperStarAdjunction
                  (ModuleCat.{u + 1} A) i).counit.app
                    (R((p)_*[ModuleCat.{u + 1} A]).obj
                      (D((k)_!open[ModuleCat.{u + 1} A]).obj K))) ∧
      (∀ {U V W Z S T : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        [IsNoetherian S] [IsNoetherian T]
        (k : U ⟶ V) (r₁ : U ⟶ W) (p₁ : V ⟶ Z) (i₁ : W ⟶ Z)
        (r₂ : W ⟶ S) (p₂ : Z ⟶ T) (i₂ : S ⟶ T)
        [IsOpenImmersion k] [IsOpenImmersion i₁] [IsOpenImmersion i₂]
        [IsProper r₁] [IsProper p₁] [IsProper r₂] [IsProper p₂]
        (sq₁ : CommSq k r₁ p₁ i₁) (sq₂ : CommSq i₁ r₂ p₂ i₂)
        (K : DerivedCategoryModule A U),
        (Γ k (r₁ ≫ r₂) (p₁ ≫ p₂) i₂ (sq₁.vert_comp sq₂)).hom.app K =
          D((i₂)_!open[ModuleCat.{u + 1} A]).map
              ((rightDerivedLowerStarComp (ModuleCat.{u + 1} A) r₁ r₂).inv.app K) ≫
            (Γ i₁ r₂ p₂ i₂ sq₂).hom.app (R((r₁)_*[ModuleCat.{u + 1} A]).obj K) ≫
            R((p₂)_*[ModuleCat.{u + 1} A]).map ((Γ k r₁ p₁ i₁ sq₁).hom.app K) ≫
            (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p₁ p₂).hom.app
              (D((k)_!open[ModuleCat.{u + 1} A]).obj K)) ∧
      (∀ {U V T W Z S : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian T] [IsNoetherian W]
        [IsNoetherian Z] [IsNoetherian S]
        (k : U ⟶ V) (l : V ⟶ T) (r : U ⟶ W) (p : V ⟶ Z) (q : T ⟶ S)
        (i : W ⟶ Z) (j : Z ⟶ S)
        [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
        [IsProper r] [IsProper p] [IsProper q]
        (sq₁ : CommSq k r p i) (sq₂ : CommSq l p q j)
        (K : DerivedCategoryModule A U),
        (Γ (k ≫ l) r q (i ≫ j) (sq₁.horiz_comp sq₂)).hom.app K =
          (Functor.mapDerivedCategoryNatIso
              (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) i j) ≪≫
            (Functor.mapDerivedCategoryCompIso _ _).symm).hom.app
              (R((r)_*[ModuleCat.{u + 1} A]).obj K) ≫
            D((j)_!open[ModuleCat.{u + 1} A]).map ((Γ k r p i sq₁).hom.app K) ≫
            (Γ l p q j sq₂).hom.app (D((k)_!open[ModuleCat.{u + 1} A]).obj K) ≫
            R((q)_*[ModuleCat.{u + 1} A]).map
              ((Functor.mapDerivedCategoryNatIso
                  (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) k l) ≪≫
                (Functor.mapDerivedCategoryCompIso _ _).symm).inv.app K)) ∧
      (∀ {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
        (k : U ⟶ V) [IsOpenImmersion k] (K : DerivedCategoryModule A U),
        (Γ k (𝟙 U) (𝟙 V) k ⟨by simp⟩).hom.app K =
          D((k)_!open[ModuleCat.{u + 1} A]).map
              ((((𝟙 U)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorIsoMapDerivedCategory ≪≫
                Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) U) ≪≫
                Functor.mapDerivedCategoryIdIso _).hom.app K) ≫
            ((((𝟙 V)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorIsoMapDerivedCategory ≪≫
                Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) V) ≪≫
                Functor.mapDerivedCategoryIdIso _).inv.app
                  (D((k)_!open[ModuleCat.{u + 1} A]).obj K))) ∧
      (∀ {U W : Scheme.{u}} [IsNoetherian U] [IsNoetherian W]
        (r : U ⟶ W) [IsProper r] (K : DerivedCategoryModule A U),
        (Γ (𝟙 U) r r (𝟙 W) ⟨by simp⟩).hom.app K =
          (Functor.mapDerivedCategoryNatIso
              (Adjunction.leftAdjointIdIso
                (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 W))
                (upperStarId (ModuleCat.{u + 1} A) W)) ≪≫
            Functor.mapDerivedCategoryIdIso _).hom.app
              (R((r)_*[ModuleCat.{u + 1} A]).obj K) ≫
            R((r)_*[ModuleCat.{u + 1} A]).map
              ((Functor.mapDerivedCategoryNatIso
                  (Adjunction.leftAdjointIdIso
                    (openImmersionLowerShriekUpperStarAdjunction
                      (ModuleCat.{u + 1} A) (𝟙 U))
                    (upperStarId (ModuleCat.{u + 1} A) U)) ≪≫
                Functor.mapDerivedCategoryIdIso _).inv.app K)) ∧
      (∀ {U V W Z U₁ V₁ W₁ Z₁ : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        [IsNoetherian U₁] [IsNoetherian V₁] [IsNoetherian W₁] [IsNoetherian Z₁]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        (k₁ : U₁ ⟶ V₁) (r₁ : U₁ ⟶ W₁) (p₁ : V₁ ⟶ Z₁) (i₁ : W₁ ⟶ Z₁)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        [IsOpenImmersion k₁] [IsOpenImmersion i₁] [IsProper r₁] [IsProper p₁]
        (sq : CommSq k r p i) (sq₁ : CommSq k₁ r₁ p₁ i₁)
        (a : V₁ ⟶ V) (b : Z₁ ⟶ Z) (c : W₁ ⟶ W) (d : U₁ ⟶ U)
        (sp : IsPullback a p₁ p b) (sr : IsPullback d r₁ r c)
        (si : IsPullback c i₁ i b) (sk : IsPullback d k₁ k a)
        (K : DerivedCategoryModule A U),
        D((b)^*[ModuleCat.{u + 1} A]).map ((Γ k r p i sq).hom.app K) ≫
            (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sp.toCommSq).app
              (D((k)_!open[ModuleCat.{u + 1} A]).obj K) ≫
            R((p₁)_*[ModuleCat.{u + 1} A]).map
              ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
                (ModuleCat.{u + 1} A) sk).inv.app K) =
          (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
              (ModuleCat.{u + 1} A) si).inv.app
                (R((r)_*[ModuleCat.{u + 1} A]).obj K) ≫
            D((i₁)_!open[ModuleCat.{u + 1} A]).map
              ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sr.toCommSq).app K) ≫
            (Γ k₁ r₁ p₁ i₁ sq₁).hom.app (D((d)^*[ModuleCat.{u + 1} A]).obj K)) := by
  classical
  let θ : ∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i),
        (r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅
          (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A] :=
    fun {U V W Z} _ _ _ _ k r p i _ _ _ _ sq => (exists_sheafComparison A k r p i sq).choose
  have hθ : (∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i)
        (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (θ k r p i sq).hom.app F ≫
            (p)_*[ModuleCat.{u + 1} A].map
              ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) k p).hom.app F =
          (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
              ((r)_*[ModuleCat.{u + 1} A].obj F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq.w).hom.app F) := by
    intro U V W Z _ _ _ _ k r p i _ _ _ _ sq F
    exact (exists_sheafComparison A k r p i sq).choose_spec F
  let Γ : ∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i),
        R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i)_!open[ModuleCat.{u + 1} A]) ≅
          D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]) :=
    fun {U V W Z} _ _ _ _ k r p i _ _ _ _ sq =>
      (constructedDerivedComparison
        (C₀ := Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
        (C₁ := Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
        (C₂ := Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A))
        (C₃ := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
        (r)_*[ModuleCat.{u + 1} A] (p)_*[ModuleCat.{u + 1} A]
        (k)_!open[ModuleCat.{u + 1} A] (i)_!open[ModuleCat.{u + 1} A]
        (fun J _ => openExtension_derivedUnit_isIso A k r p i sq J) (θ k r p i sq)).comparison
  have hΓ : (∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i)
        (J : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [J.IsKInjective]
        (I : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [I.IsKInjective]
        (ρ : ((k)_!open[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J ⟶ I)
        [QuasiIso ρ],
        D((i)_!open[ModuleCat.{u + 1} A]).map
            (((r)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso J).hom ≫
          ((i)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app
            (((r)_*[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (θ k r p i sq).hom (.up ℤ)).app J) ≫
          DerivedCategory.Q.map
            (((p)_*[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).map ρ) =
        (Γ k r p i sq).hom.app (DerivedCategory.Q.obj J) ≫
          R((p)_*[ModuleCat.{u + 1} A]).map
            (((k)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app J ≫
              DerivedCategory.Q.map ρ) ≫
          (((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso I).hom) := by
    intro U V W Z _ _ _ _ k r p i _ _ _ _ sq J _ I _ ρ _
    exact (constructedDerivedComparison
      (C₀ := Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
      (C₁ := Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
      (C₂ := Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A))
      (C₃ := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
      (r)_*[ModuleCat.{u + 1} A] (p)_*[ModuleCat.{u + 1} A]
      (k)_!open[ModuleCat.{u + 1} A] (i)_!open[ModuleCat.{u + 1} A]
      (fun J _ => openExtension_derivedUnit_isIso A k r p i sq J)
      (θ k r p i sq)).representative_normalization J I ρ
  have hΓh : (∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (sq : CommSq k r p i)
        (X : HomotopyCategory
          (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)),
      ((i)_!open[ModuleCat.{u + 1} A]).mapDerivedCategory.map
          (((r)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorUnit.app X) ≫
          (Γ k r p i sq).hom.app (DerivedCategory.Qh.obj X) =
        ((i)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactorsh.hom.app
          ((((r)_*[ModuleCat.{u + 1} A]).mapHomotopyCategory (.up ℤ)).obj X) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory (θ k r p i sq).hom (.up ℤ)).app X) ≫
          ((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorUnit.app
            ((((k)_!open[ModuleCat.{u + 1} A]).mapHomotopyCategory (.up ℤ)).obj X) ≫
          ((p)_*[ModuleCat.{u + 1} A]).rightDerivedFunctor.map
            (((k)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactorsh.inv.app X)) := by
    intro U V W Z _ _ _ _ k r p i _ _ _ _ sq X
    exact (constructedDerivedComparison
      (C₀ := Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
      (C₁ := Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
      (C₂ := Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A))
      (C₃ := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
      (r)_*[ModuleCat.{u + 1} A] (p)_*[ModuleCat.{u + 1} A]
      (k)_!open[ModuleCat.{u + 1} A] (i)_!open[ModuleCat.{u + 1} A]
      (fun J _ => openExtension_derivedUnit_isIso A k r p i sq J)
      (θ k r p i sq)).unit_normalization X
  clear_value Γ θ
  obtain ⟨hv, hh, hip, hio⟩ :=
    unboundedProperOpenPasting_of_normalization A @θ @Γ hθ hΓh
  exact ⟨@θ, @Γ, hθ, hΓ,
    unboundedProperOpenAdjunctionNormalization_of_normalization A @θ @Γ hθ hΓ,
    hv, hh, hip, hio,
    unboundedProperOpenBaseChange_of_normalization A @θ @Γ hθ hΓ⟩

end AlgebraicGeometry.Etale
