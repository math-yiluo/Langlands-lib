/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
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
public import Mathlib.CategoryTheory.Sites.Limits
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
public import Mathlib.Algebra.Homology.Additive
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
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
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
import WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
import WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.CategoryTheory.Sites.Subsheaf
import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
import WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.ProperMorphismFpqcDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.AlgebraicGeometry.ProperSupportCompositeRange
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
import WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.AlgebraicGeometry.ProperSupportExchangeRange
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility
import WeilConjectures.SecSmoothPurity.ProperSupportPullbackSectionMap
import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalk
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Defs
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.AlgebraicGeometry.ProperGeometricPointExchange
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.ProperStrictLocalFibreSections
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import WeilConjectures.AlgebraicGeometry.QcqsGeometricExchangeFactorization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
import WeilConjectures.AlgebraicGeometry.EtaleUnitSectionRestriction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import WeilConjectures.AlgebraicGeometry.SmallStrictLocalSectionMaps
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointCanonicalGerm
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalkCore
import WeilConjectures.Compactification.BaseChange
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenCompositionSupplement
public import WeilConjectures.AlgebraicGeometry.UnboundedProperOpenPasting

/-!
# Unbounded proper/open Pasting

Source: Stacks Project, Tags 0F7C and 0F7D.
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

private theorem exact_identity_fac
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory A]
    (E : A ⥤ A) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (e : E ≅ 𝟭 A) (J : HomotopyCategory A (.up ℤ)) :
    (Functor.mapDerivedCategoryNatIso e ≪≫
        Functor.mapDerivedCategoryIdIso A).hom.app (DerivedCategory.Qh.obj J) =
      E.mapDerivedCategoryFactorsh.hom.app J ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app J) := by
  simp only [Iso.trans_hom, NatTrans.comp_app]
  rw [Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj, Functor.mapDerivedCategoryNatIso_fach]

private theorem ordinary_identity_vertical
    (Λ : Type (u + 1)) [CommRing Λ] {A B : Scheme.{u}}
    (k : A ⟶ B) [IsOpenImmersion k]
    (δ : lowerStar (ModuleCat.{u + 1} Λ) (𝟙 A) ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ⋙
        lowerStar (ModuleCat.{u + 1} Λ) (𝟙 B))
    (hn : ∀ F, δ.hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) (𝟙 B)).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) k (𝟙 B)).hom.app F =
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app
          ((lowerStar (ModuleCat.{u + 1} Λ) (𝟙 A)).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) (𝟙 A) k (k ≫ 𝟙 B)
            ((Category.comp_id k).trans (Category.id_comp k).symm)).hom.app F)
    (F : Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    δ.hom.app F ≫ (lowerStarId (ModuleCat.{u + 1} Λ) B).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).obj F) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).map
        ((lowerStarId (ModuleCat.{u + 1} Λ) A).hom.app F) := by
  have := mono_openImmersionLowerShriekToLowerStar_app Λ k F
  apply (cancel_mono
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F)).1
  have hnaux (f : A ⟶ B) (hf : f = k ≫ 𝟙 B) :
      δ.hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) (𝟙 B)).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) k (𝟙 B) f hf).hom.app F =
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app
          ((lowerStar (ModuleCat.{u + 1} Λ) (𝟙 A)).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) (𝟙 A) k f
            (hf.trans ((Category.comp_id k).trans (Category.id_comp k).symm))).hom.app F := by
    subst f
    exact hn F
  have hn' : δ.hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) (𝟙 B)).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) k (𝟙 B) k
            (Category.comp_id k).symm).hom.app F =
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app
          ((lowerStar (ModuleCat.{u + 1} Λ) (𝟙 A)).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) (𝟙 A) k k
            (Category.id_comp k).symm).hom.app F := by
    exact hnaux k (Category.comp_id k).symm
  rw [lowerStarComp_id_right, lowerStarComp_id_left] at hn'
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app] at hn'
  erw [Category.comp_id, Category.comp_id] at hn'
  simp only [Category.assoc]
  have hid := (lowerStarId (ModuleCat.{u + 1} Λ) B).hom.naturality
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F)
  simp only [Functor.id_map] at hid
  rw [← hid, hn']
  exact ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).naturality
    ((lowerStarId (ModuleCat.{u + 1} Λ) A).hom.app F)).symm

private theorem open_identity_comparison
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) (𝟙 X)).app F ≫
        (lowerStarId (ModuleCat.{u + 1} Λ) X).hom.app F =
      (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X))
        (upperStarId (ModuleCat.{u + 1} Λ) X)).hom.app F := by
  let adj := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)
  let e := upperStarId (ModuleCat.{u + 1} Λ) X
  let l := Adjunction.leftAdjointIdIso adj e
  apply (adj.homEquiv F F).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hl := unit_conjugateEquiv Adjunction.id adj l.hom F
  rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom] at hl
  have hl' : e.inv.app F = adj.unit.app F ≫
      (upperStar (ModuleCat.{u + 1} Λ) (𝟙 X)).map (l.hom.app F) := by
    change 𝟙 F ≫ e.inv.app F = _ at hl
    simpa only [Category.id_comp] using hl
  erw [← hl']
  have hh : (upperStar (ModuleCat.{u + 1} Λ) (𝟙 X)).map
        ((lowerStarId (ModuleCat.{u + 1} Λ) X).hom.app F) =
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)).counit.app F ≫
        e.inv.app F := by
    apply (cancel_mono (e.hom.app F)).1
    rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    have hn := e.hom.naturality ((lowerStarId (ModuleCat.{u + 1} Λ) X).hom.app F)
    simp only [Functor.id_map] at hn
    erw [hn, ← upperStarId_inv_app_counit_app, Iso.hom_inv_id_app_assoc]
  rw [CategoryTheory.Functor.map_comp]
  erw [hh]
  have hn := unit_map_openImmersionLowerShriekToLowerStar_app_counit
    (ModuleCat.{u + 1} Λ) (𝟙 X) F
  have hn' := congrArg (fun z ↦ z ≫ e.inv.app F) hn
  erw [Category.id_comp] at hn'
  simpa only [Category.assoc] using hn'

private theorem ordinary_identity_horizontal
    (Λ : Type (u + 1)) [CommRing Λ]
    {A C : Scheme.{u}} (r : A ⟶ C)
    (δ : lowerStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (𝟙 C) ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (𝟙 A) ⋙
        lowerStar (ModuleCat.{u + 1} Λ) r)
    (hn : ∀ F, δ.hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) r).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) (𝟙 A)).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) (𝟙 A) r).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) (𝟙 C)).app
        ((lowerStar (ModuleCat.{u + 1} Λ) r).obj F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) r (𝟙 C) ((𝟙 A) ≫ r)
          ((Category.id_comp r).trans (Category.comp_id r).symm)).hom.app F)
    (F : Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    δ.hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) r).map
        ((Adjunction.leftAdjointIdIso
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 A))
          (upperStarId (ModuleCat.{u + 1} Λ) A)).hom.app F) =
      (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 C))
        (upperStarId (ModuleCat.{u + 1} Λ) C)).hom.app
          ((lowerStar (ModuleCat.{u + 1} Λ) r).obj F) := by
  have hnaux (f : A ⟶ C) (hf : f = (𝟙 A) ≫ r) :
      δ.hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) r).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) (𝟙 A)).app F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) (𝟙 A) r f hf).hom.app F =
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) (𝟙 C)).app
          ((lowerStar (ModuleCat.{u + 1} Λ) r).obj F) ≫
          (lowerStarComp (ModuleCat.{u + 1} Λ) r (𝟙 C) f
            (hf.trans ((Category.id_comp r).trans (Category.comp_id r).symm))).hom.app F := by
    subst f
    exact hn F
  have hn' := hnaux r (Category.id_comp r).symm
  rw [lowerStarComp_id_left, lowerStarComp_id_right] at hn'
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.leftUnitor_hom_app,
    Functor.rightUnitor_hom_app] at hn'
  erw [Category.comp_id, Category.comp_id] at hn'
  rw [← open_identity_comparison Λ A F,
    ← open_identity_comparison Λ C ((lowerStar (ModuleCat.{u + 1} Λ) r).obj F),
    CategoryTheory.Functor.map_comp, ← Category.assoc]
  exact hn'

private theorem derived_vertical_identity
    {A B : Type v} [Category.{w} A] [Category.{w} B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (G : A ⥤ A) (H : B ⥤ B) (E : A ⥤ B)
    [G.Additive] [H.Additive] [E.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (eG : G ≅ 𝟭 A) (eH : H ≅ 𝟭 B) (δ : G ⋙ E ⟶ E ⋙ H)
    (γ : G.rightDerivedFunctor ⋙ E.mapDerivedCategory ⟶
      E.mapDerivedCategory ⋙ H.rightDerivedFunctor)
    (hδ : ∀ F, δ.app F ≫ eH.hom.app (E.obj F) = E.map (eG.hom.app F))
    (hγ : ∀ J : HomotopyCategory A (.up ℤ),
      E.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app J) ≫
        γ.app (DerivedCategory.Qh.obj J) =
      E.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj J) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory δ (.up ℤ)).app J) ≫
        H.rightDerivedFunctorUnit.app ((E.mapHomotopyCategory (.up ℤ)).obj J) ≫
        H.rightDerivedFunctor.map (E.mapDerivedCategoryFactorsh.inv.app J))
    (ia : G.rightDerivedFunctor ⟶ 𝟭 (DerivedCategory A))
    (ib : H.rightDerivedFunctor ≅ 𝟭 (DerivedCategory B))
    (ha : ∀ J, G.rightDerivedFunctorUnit.app J ≫
      ia.app (DerivedCategory.Qh.obj J) =
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory eG.hom (.up ℤ)).app J))
    (hb : ∀ J, H.rightDerivedFunctorUnit.app J ≫
      ib.hom.app (DerivedCategory.Qh.obj J) =
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory eH.hom (.up ℤ)).app J))
    (K : DerivedCategory A) :
    γ.app K = E.mapDerivedCategory.map (ia.app K) ≫
      ib.inv.app (E.mapDerivedCategory.obj K) := by
  let a : G.rightDerivedFunctor ⋙ E.mapDerivedCategory ⟶
      E.mapDerivedCategory := γ ≫ Functor.whiskerLeft E.mapDerivedCategory ib.hom
  let b : G.rightDerivedFunctor ⋙ E.mapDerivedCategory ⟶
      E.mapDerivedCategory := Functor.whiskerRight ia E.mapDerivedCategory
  have : (G.rightDerivedFunctor ⋙ E.mapDerivedCategory).IsRightDerivedFunctor
      (Functor.whiskerRight G.rightDerivedFunctorUnit E.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.quasiIso A (.up ℤ)) := by
    refine (HomotopyCategory.KInjectives.localizerMorphism_derives
      (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⋙
        E.mapDerivedCategory)).isRightDerivedFunctor_of_isIso _ (fun X => ?_)
    obtain ⟨J, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app]
    have hi : IsIso (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient A (.up ℤ)).obj J)) := inferInstance
    change IsIso (E.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient A (.up ℤ)).obj J)) ≫ 𝟙 _)
    infer_instance
  have hab : a = b := by
    apply Functor.rightDerived_ext (G.rightDerivedFunctor ⋙ E.mapDerivedCategory)
      (Functor.whiskerRight G.rightDerivedFunctorUnit E.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.quasiIso A (.up ℤ))
    apply NatTrans.ext
    funext J
    simp only [a, b, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Category.assoc]
    simp only [Functor.comp_obj]
    erw [Category.id_comp, Category.id_comp]
    erw [reassoc_of% hγ J]
    have hn := ib.hom.naturality (E.mapDerivedCategoryFactorsh.inv.app J)
    simp only [Functor.id_map] at hn
    erw [hn]
    erw [reassoc_of% hb ((E.mapHomotopyCategory (.up ℤ)).obj J)]
    have ht : δ ≫ Functor.whiskerLeft E eH.hom =
        Functor.whiskerRight eG.hom E := by
      ext F
      exact hδ F
    have hh := congr_app (congrArg (fun t => NatTrans.mapHomotopyCategory t (.up ℤ)) ht) J
    simp only [NatTrans.mapHomotopyCategory_comp, NatTrans.comp_app] at hh
    change (NatTrans.mapHomotopyCategory δ (.up ℤ)).app J ≫
        (NatTrans.mapHomotopyCategory eH.hom (.up ℤ)).app ((E.mapHomotopyCategory (.up ℤ)).obj J) =
      (E.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory eG.hom (.up ℤ)).app J) at hh
    erw [← DerivedCategory.Qh.map_comp_assoc, hh]
    have he := E.mapDerivedCategoryFactorsh.hom.naturality
      ((NatTrans.mapHomotopyCategory eG.hom (.up ℤ)).app J)
    simp only [Functor.comp_map] at he
    erw [← reassoc_of% he]
    erw [E.mapDerivedCategoryFactorsh.hom_inv_id_app J, Category.comp_id]
    erw [← E.mapDerivedCategory.map_comp, ha]
  apply (cancel_mono (ib.hom.app (E.mapDerivedCategory.obj K))).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  exact congr_app hab K

private theorem derived_horizontal_identity
    {A B : Type v} [Category.{w} A] [Category.{w} B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (G : A ⥤ B) (E : A ⥤ A) (F : B ⥤ B)
    [G.Additive] [E.Additive] [F.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (eE : E ≅ 𝟭 A) (eF : F ≅ 𝟭 B) (δ : G ⋙ F ≅ E ⋙ G)
    (γ : G.rightDerivedFunctor ⋙ F.mapDerivedCategory ≅
      E.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (hδ : ∀ X, δ.hom.app X ≫ G.map (eE.hom.app X) = eF.hom.app (G.obj X))
    (hγ : ∀ J : HomotopyCategory A (.up ℤ),
      F.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app J) ≫
        γ.hom.app (DerivedCategory.Qh.obj J) =
      F.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj J) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory δ.hom (.up ℤ)).app J) ≫
        G.rightDerivedFunctorUnit.app ((E.mapHomotopyCategory (.up ℤ)).obj J) ≫
        G.rightDerivedFunctor.map (E.mapDerivedCategoryFactorsh.inv.app J))
    (K : DerivedCategory A) :
    γ.hom.app K =
      (Functor.mapDerivedCategoryNatIso eF ≪≫
        Functor.mapDerivedCategoryIdIso B).hom.app (G.rightDerivedFunctor.obj K) ≫
      G.rightDerivedFunctor.map ((Functor.mapDerivedCategoryNatIso eE ≪≫
        Functor.mapDerivedCategoryIdIso A).inv.app K) := by
  let eED := Functor.mapDerivedCategoryNatIso eE ≪≫
    Functor.mapDerivedCategoryIdIso A
  let eFD := Functor.mapDerivedCategoryNatIso eF ≪≫
    Functor.mapDerivedCategoryIdIso B
  let a : G.rightDerivedFunctor ⋙ F.mapDerivedCategory ⟶
      G.rightDerivedFunctor :=
    γ.hom ≫ Functor.whiskerRight eED.hom G.rightDerivedFunctor
  let b : G.rightDerivedFunctor ⋙ F.mapDerivedCategory ⟶
      G.rightDerivedFunctor := Functor.whiskerLeft G.rightDerivedFunctor eFD.hom
  have : (G.rightDerivedFunctor ⋙ F.mapDerivedCategory).IsRightDerivedFunctor
      (Functor.whiskerRight G.rightDerivedFunctorUnit F.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.quasiIso A (.up ℤ)) := by
    refine (HomotopyCategory.KInjectives.localizerMorphism_derives
      (G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⋙
        F.mapDerivedCategory)).isRightDerivedFunctor_of_isIso _ (fun X => ?_)
    obtain ⟨J, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app]
    have hi : IsIso (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient A (.up ℤ)).obj J)) := inferInstance
    change IsIso (F.mapDerivedCategory.map (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient A (.up ℤ)).obj J)) ≫ 𝟙 _)
    infer_instance
  have hab : a = b := by
    apply Functor.rightDerived_ext (G.rightDerivedFunctor ⋙ F.mapDerivedCategory)
      (Functor.whiskerRight G.rightDerivedFunctorUnit F.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.quasiIso A (.up ℤ))
    apply NatTrans.ext
    funext J
    simp only [a, b, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Category.assoc]
    simp only [Functor.comp_obj]
    erw [Category.id_comp, Category.id_comp]
    erw [reassoc_of% hγ J]
    erw [← G.rightDerivedFunctor.map_comp, exact_identity_fac E eE J,
      Iso.inv_hom_id_app_assoc]
    have hn := G.rightDerivedFunctorUnit.naturality
      ((NatTrans.mapHomotopyCategory eE.hom (.up ℤ)).app J)
    simp only [Functor.comp_map] at hn
    erw [← hn]
    have hf := eFD.hom.naturality (G.rightDerivedFunctorUnit.app J)
    simp only [Functor.id_map] at hf
    erw [hf, exact_identity_fac F eF ((G.mapHomotopyCategory (.up ℤ)).obj J)]
    have ht : δ.hom ≫ Functor.whiskerRight eE.hom G =
        Functor.whiskerLeft G eF.hom := by
      ext X
      exact hδ X
    have hh := congr_app (congrArg (fun t => NatTrans.mapHomotopyCategory t (.up ℤ)) ht) J
    simp only [NatTrans.mapHomotopyCategory_comp, NatTrans.comp_app] at hh
    change (NatTrans.mapHomotopyCategory δ.hom (.up ℤ)).app J ≫
        (G.mapHomotopyCategory (.up ℤ)).map ((NatTrans.mapHomotopyCategory eE.hom (.up ℤ)).app J) =
      (NatTrans.mapHomotopyCategory eF.hom (.up ℤ)).app
        ((G.mapHomotopyCategory (.up ℤ)).obj J) at hh
    erw [← DerivedCategory.Qh.map_comp_assoc, hh]
    erw [Category.assoc]
    rfl
  apply (cancel_mono (G.rightDerivedFunctor.map (eED.hom.app K))).1
  change γ.hom.app K ≫ G.rightDerivedFunctor.map (eED.hom.app K) =
    (eFD.hom.app (G.rightDerivedFunctor.obj K) ≫
      G.rightDerivedFunctor.map (eED.inv.app K)) ≫
        G.rightDerivedFunctor.map (eED.hom.app K)
  rw [Category.assoc, ← G.rightDerivedFunctor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact congr_app hab K

private theorem derived_identity_fac
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory A]
    [Abelian.HasKInjectiveResolutions A]
    (G : A ⥤ A) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : G ≅ 𝟭 A) (J : HomotopyCategory A (.up ℤ)) :
    G.rightDerivedFunctorUnit.app J ≫
      (G.rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryNatIso e ≪≫
        Functor.mapDerivedCategoryIdIso A).hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app J) := by
  have hf := congr_app G.rightDerivedFunctorIsoMapDerivedCategory_hom_fac J
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
  change G.rightDerivedFunctorUnit.app J ≫
    G.rightDerivedFunctorIsoMapDerivedCategory.hom.app _ ≫
    (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso A).hom.app _ = _
  rw [← Category.assoc, hf, exact_identity_fac, Iso.inv_hom_id_app_assoc]

/-- Pasting and identities for comparisons normalized by the homotopy derived units.
Source: Stacks Project, Tags 0F7C and 0F7D, including their identity cases.
(blueprint: lem-amb-unbounded-proper-open-pasting).

Proof:
The two composition equations are the conclusions of the separate composition theorem.
For proper identity edges, include the sheaf comparison into the common direct image.
The support normalization, naturality and the direct-image identity compositor imply
that theta followed by the target identity map is k! of the source identity map.
For open identity edges use the same monic-inclusion argument and the two open-adjunction
triangle identities to identify theta with the open identity comparisons. In either case,
right-derived transformation uniqueness transports this ordinary identity to derived
categories: precompose with the derived unit, use the assumed unit normalization,
move the identity comparison past the unit by naturality, and use its termwise
factorization. The exact identity factorization follows from the exact-derived natural
isomorphism and identity APIs; for proper identity maps also compose with the comparison
between the right-derived and exact-derived functors. Cancel the resulting invertible
identity comparison to obtain each displayed formula. This argument uses K-injectives
only to establish the derivability structure and imposes no boundedness condition.
-/
theorem unboundedProperOpenPasting_of_normalization (A : Type (u + 1)) [CommRing A] [Finite A]
    (θ : ∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (_sq : CommSq k r p i),
        (r)_*[ModuleCat.{u + 1} A] ⋙ (i)_!open[ModuleCat.{u + 1} A] ≅
          (k)_!open[ModuleCat.{u + 1} A] ⋙ (p)_*[ModuleCat.{u + 1} A])
    (Γ : ∀ {U V W Z : Scheme.{u}}
        [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
        (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
        [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
        (_sq : CommSq k r p i),
        R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i)_!open[ModuleCat.{u + 1} A]) ≅
          D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]))
    (hθ : (∀ {U V W Z : Scheme.{u}}
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
            (lowerStarComp (ModuleCat.{u + 1} A) r i (k ≫ p) sq.w).hom.app F))
    (hΓ : (∀ {U V W Z : Scheme.{u}}
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
            (((k)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactorsh.inv.app X))) :
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
                Functor.mapDerivedCategoryIdIso _).inv.app K)) := by
  obtain ⟨hv, hh⟩ := unboundedProperOpenComposition_of_normalization A θ Γ hθ hΓ
  refine ⟨hv, hh, ?_, ?_⟩
  · intro U V _ _ k _ K
    exact derived_vertical_identity
      (lowerStar (ModuleCat.{u + 1} A) (𝟙 U))
      (lowerStar (ModuleCat.{u + 1} A) (𝟙 V))
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) k)
      (lowerStarId (ModuleCat.{u + 1} A) U)
      (lowerStarId (ModuleCat.{u + 1} A) V)
      (θ k (𝟙 U) (𝟙 V) k ⟨by simp⟩).hom
      (Γ k (𝟙 U) (𝟙 V) k ⟨by simp⟩).hom
      (ordinary_identity_vertical A k (θ k (𝟙 U) (𝟙 V) k ⟨by simp⟩)
        (hθ k (𝟙 U) (𝟙 V) k ⟨by simp⟩))
      (hΓ k (𝟙 U) (𝟙 V) k ⟨by simp⟩)
      (((((𝟙 U)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) U) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom))
      (((𝟙 V)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) V) ≪≫
        Functor.mapDerivedCategoryIdIso _)
      (derived_identity_fac _ (lowerStarId (ModuleCat.{u + 1} A) U))
      (derived_identity_fac _ (lowerStarId (ModuleCat.{u + 1} A) V)) K
  · intro U W _ _ r _ K
    let eU := Adjunction.leftAdjointIdIso
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 U))
      (upperStarId (ModuleCat.{u + 1} A) U)
    let eW := Adjunction.leftAdjointIdIso
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 W))
      (upperStarId (ModuleCat.{u + 1} A) W)
    exact derived_horizontal_identity (lowerStar (ModuleCat.{u + 1} A) r)
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) (𝟙 U))
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) (𝟙 W)) eU eW
      (θ (𝟙 U) r r (𝟙 W) ⟨by simp⟩) (Γ (𝟙 U) r r (𝟙 W) ⟨by simp⟩)
      (ordinary_identity_horizontal A r (θ (𝟙 U) r r (𝟙 W) ⟨by simp⟩)
        (hθ (𝟙 U) r r (𝟙 W) ⟨by simp⟩))
      (hΓ (𝟙 U) r r (𝟙 W) ⟨by simp⟩) K

end AlgebraicGeometry.Etale
