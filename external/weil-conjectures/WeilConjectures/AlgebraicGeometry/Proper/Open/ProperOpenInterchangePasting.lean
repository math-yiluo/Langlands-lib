/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedExtensionZeroBaseChangeSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import all WeilConjectures.AlgebraicGeometry.EtaleProperOpenHorizontalNormalization
import all WeilConjectures.AlgebraicGeometry.DerivedCategories
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.AlgebraicGeometry.Sites.Etale
import all WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import all Mathlib.AlgebraicGeometry.Morphisms.Proper
import all WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.CategoryTheory.Adjunction.CompositionIso
import all WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import all WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.GeometricRingTransport
import all Mathlib.CategoryTheory.Sites.Limits
import all WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import all WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import all WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
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
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
import all WeilConjectures.AlgebraicGeometry.EtaleSheaves
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import all WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import all WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import all Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import all Mathlib.AlgebraicGeometry.Scheme
import all Mathlib.CategoryTheory.Sites.Point.Basic
import all Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import all WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import all Mathlib.AlgebraicGeometry.Sites.EtalePoint
import all WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
import all WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
import all WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import all Mathlib.CategoryTheory.Sites.Subsheaf
import all WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import all WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen
import all WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
import all WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
import all WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
import all Mathlib.AlgebraicGeometry.Morphisms.Etale
import all Mathlib.AlgebraicGeometry.Pullbacks
import all WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import all WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
import all Mathlib.AlgebraicGeometry.Sites.Fpqc
import all WeilConjectures.AlgebraicGeometry.ProperMorphismFpqcDescent
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import all WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import all WeilConjectures.AlgebraicGeometry.ProperSupportCompositeRange
import all WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
import all WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
import all WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import all WeilConjectures.AlgebraicGeometry.ProperSupportExchangeRange
import all WeilConjectures.SixFunctors.BaseChange.Square
import all WeilConjectures.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility
import all WeilConjectures.SecSmoothPurity.ProperSupportPullbackSectionMap
import all WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalk
import all WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import all WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import all WeilConjectures.Compactification.NagataCompactification
import all WeilConjectures.Compactification.Defs
import all WeilConjectures.SixFunctors.OpenClosed.Complex
import all WeilConjectures.AlgebraicGeometry.ProperGeometricPointExchange
import all Mathlib.FieldTheory.IsAlgClosed.Basic
import all WeilConjectures.AlgebraicGeometry.ProperStrictLocalFibreSections
import all WeilConjectures.Mathlib.RingTheory.Henselian
import all WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import all WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import all WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import all WeilConjectures.AlgebraicGeometry.QcqsGeometricExchangeFactorization
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import all Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import all Mathlib.AlgebraicGeometry.ResidueField
import all Mathlib.FieldTheory.IsSepClosed
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import all WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import all WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import all WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import all WeilConjectures.RingTheory.StrictHenselizationTriples
import all WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
import all WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import all WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
import all WeilConjectures.AlgebraicGeometry.EtaleUnitSectionRestriction
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import all WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import all WeilConjectures.AlgebraicGeometry.SmallStrictLocalSectionMaps
import all WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
import all WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointCanonicalGerm
import all WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import all WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalkCore
import all WeilConjectures.Compactification.BaseChange
import all Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import all WeilConjectures.SixFunctors.OpenClosed.Exact
import all WeilConjectures.SixFunctors.BaseChange.Pasting
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeNaturality

/-!
# Horizontal pasting for normalized proper/open interchange

## References

* Stacks Project, More on Etale Cohomology, Tags 0F7B, 0F7C, 0F7D and 0F7F
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

set_option linter.unusedVariables false in
/-- Horizontal pasting for normalized proper/open interchange.
The ordinary and derived isomorphisms are supplied. The derived map is the
canonical rightDerivedFunctorPlusBaseChange of the ordinary map;
this theorem asserts only the indicated equalities for those fixed isomorphisms.
-/
theorem properOpenInterchangeHorizontalPasting_of_normalization (Λ : Type (u + 1)) [CommRing Λ]
  [Finite Λ]
    (δ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion
        k] [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), (lowerStar
        (ModuleCat.{u + 1} Λ) r) ⋙ (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i) ≅
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k) ⋙ (lowerStar (ModuleCat.{u + 1} Λ) p))
      (γ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion
        k] [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
        ((lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus) ⋙ (openImmersionLowerShriek
        (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ≅ (openImmersionLowerShriek (ModuleCat.{u +
        1} Λ) k).mapDerivedCategoryPlus ⋙ ((lowerStar (ModuleCat.{u + 1} Λ)
          p).rightDerivedFunctorPlus))
    (hδ : (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D)
      [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ (F : (Sheaf
        A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (δ k i r p h).hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) p).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) k p).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app ((lowerStar (ModuleCat.{u +
        1} Λ) r).obj F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) r i (k ≫ p) h).hom.app F))
    (hγ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D)
      (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion k] [IsOpenImmersion i]
      [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i),
      (γ k i r p h).hom = Functor.rightDerivedFunctorPlusBaseChange (δ k i r p h).hom) :
    (∀ {A B C D E F : Scheme.{u}}
      (k : A ⟶ B) (l : B ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C) (p : B ⟶ D) (q : E ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
      (h : (k ≫ l) ≫ q = r ≫ (i ≫ j))
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (extensionZeroCompDerivedPlusIso Λ i j).hom.app (((lowerStar (ModuleCat.{u + 1} Λ)
        r).rightDerivedFunctorPlus).obj K) ≫
        (γ (k ≫ l) (i ≫ j) r q h).hom.app K ≫
        ((lowerStar (ModuleCat.{u + 1} Λ) q).rightDerivedFunctorPlus).map
          ((extensionZeroCompDerivedPlusIso Λ
        k l).inv.app K) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.map ((γ k i r p
        h₁).hom.app K) ≫
        (γ l j p q h₂).hom.app ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
        k).mapDerivedCategoryPlus.obj K)) := by
  intro A B C D E F k l i j r p q _ _ _ _ _ _ _ h₁ h₂ h K
  let e₁ := (δ k i r p h₁).hom
  let e₂ := (δ l j p q h₂).hom
  let e := (δ (k ≫ l) (i ≫ j) r q h).hom
  let ck := openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) k l
  let ci := openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) i j
  have ho := ordinary_horizontal Λ k l r p q i j ⟨h₁⟩ ⟨h₂⟩
    (δ k i r p h₁) (δ l j p q h₂) (δ (k ≫ l) (i ≫ j) r q h)
    (hδ k i r p h₁) (hδ l j p q h₂) (hδ (k ≫ l) (i ≫ j) r q h)
  have hn : Functor.baseChangePaste e₁ e₂ ≫
      Functor.whiskerRight ck.inv (lowerStar (ModuleCat.{u + 1} Λ) q) =
      Functor.whiskerLeft (lowerStar (ModuleCat.{u + 1} Λ) r) ci.inv ≫ e := by
    apply NatTrans.ext
    funext M
    apply (cancel_mono ((lowerStar (ModuleCat.{u + 1} Λ) q).map (ck.hom.app M))).1
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.baseChangePaste, Functor.associator_inv_app, Functor.associator_hom_app,
      Category.id_comp, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    rw [ho M]
    simp only [ci, e₁, e₂, Iso.inv_hom_id_app_assoc]
    rw [(lowerStar (ModuleCat.{u + 1} Λ) q).map_id]
    erw [Category.comp_id]
  have hnD := Functor.rightDerivedFunctorPlusBaseChange_naturality
    (Functor.baseChangePaste e₁ e₂) e ci.symm ck.symm hn K
  have hpD := Functor.rightDerivedFunctorPlusBaseChange_paste e₁ e₂ K
  rw [hγ, hγ, hγ]
  change (extensionZeroCompDerivedPlusIso Λ i j).hom.app
      ((lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlus.obj K) ≫
      (Functor.rightDerivedFunctorPlusBaseChange e).app K ≫
      (lowerStar (ModuleCat.{u + 1} Λ) q).rightDerivedFunctorPlus.map
        ((extensionZeroCompDerivedPlusIso Λ k l).inv.app K) = _
  dsimp only [extensionZeroCompDerivedPlusIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app]
  simp only [Category.assoc, Functor.map_comp]
  rw [← reassoc_of% hnD]
  dsimp only [ck]
  rw [← (lowerStar (ModuleCat.{u + 1} Λ) q).rightDerivedFunctorPlus.map_comp_assoc,
    Iso.hom_inv_id_app, (lowerStar (ModuleCat.{u + 1} Λ) q).rightDerivedFunctorPlus.map_id,
    Category.id_comp]
  rw [hpD]
  simp only [Iso.inv_hom_id_app_assoc]
  rfl

end AlgebraicGeometry.Etale
