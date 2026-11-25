/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacks
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Category.Profinite.AsLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Compactness.Compact
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedIdealGenerators
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
public import WeilConjectures.AlgebraicGeometry.Constant.ConstantModelStratificationTransportSupplement
public import WeilConjectures.AlgebraicGeometry.Integral.Models.IntegralModelsStacksBlueprint
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
public import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.AlgebraicGeometry.Integral.Models.IntegralModelsEmbeddedCompletionSupplement
import WeilConjectures.AlgebraicGeometry.Integral.Models.IntegralModelsEmbeddedStacksCriterion
import WeilConjectures.AlgebraicGeometry.Integral.Models.IntegralModelsEmbeddedResidueComparison
/-! # Integral models for constructible l-adic complexes

Coefficients are the existing continuous condensed rings pulled back from the point.
The constant and completed ambient categories remain distinct. Completeness is the
existing local ringed-ideal predicate transported to the equivalent small site; the
constant-completion comparison identifies it with the canonical quotient-tower condition.

## Main definitions and statement

* `IntegralModelsEmbedded`: canonical embedded-coefficient scalar maps and predicates.
* `integralModelResidueEtaleOrigin`: bounded constructible etale origin of the first reduction.
* `integral_models`: the opening Tor-amplitude equality and all four integral-model clauses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

attribute [local irreducible] IntegralModelsStacks.smallDerivedObject
  IntegralModelsStacks.smallModules IntegralModelsStacks.smallMap
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] integralModel_coefficientMonObj in
/-- Integral constructible complexes have finite Tor amplitude. Restriction along the
canonical constant-to-completed scalar map identifies complete objects and the two
constructibility conditions. The categories are preserved by inverse image, ambient
uncompleted relative derived tensor, and locally closed extension by zero. Rational
constructible objects are generated by integral lattices under finite cones and shifts,
using one finite coefficient field per algebraic-closure object. The same integral
extension by zero has the stated derived reductions at every positive exponent.
-/
theorem integral_models
    (k : Type u) [Field k] (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime]
    [CharP k p] (hℓp : ℓ ≠ p) (X : Scheme.{u})
    [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [IsNoetherian X] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1)) :
    ((constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X ⊓
        _root_.DerivedCategory.finiteTorAmplitude _) =
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X) ∧
    (∃ e : ObjectProperty.FullSubcategory (IntegralModelsEmbedded.completedComplete ℓ E π X) ≌
        ObjectProperty.FullSubcategory (IntegralModelsEmbedded.constantComplete ℓ E π X),
      Nonempty (e.functor ⋙ ObjectProperty.ι (IntegralModelsEmbedded.constantComplete ℓ E π X) ≅
        ObjectProperty.ι (IntegralModelsEmbedded.completedComplete ℓ E π X) ⋙
          IntegralModelsEmbedded.restriction ℓ E X)) ∧
    (∀ K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (integralCoefficientObject X ℓ E)),
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X K ↔
        IntegralModelsEmbedded.stacksConstructible ℓ E π X
          ((IntegralModelsEmbedded.restriction ℓ E X).obj K)) ∧
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X K ↔
        IntegralModelsEmbedded.completedComplete ℓ E π X K ∧
          integralModelResidueEtaleOrigin X ℓ E π K)) ∧
    (∀ (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of k))]
      [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
      [IsNoetherian Y] (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
      (K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (integralCoefficientObject Y ℓ E))),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) Y K →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X
        ((CondensedRing.moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.1)
          f).obj K)) ∧
    (∀ K M : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (integralCoefficientObject X ℓ E)),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X K →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X M →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X
        (((CondensedRing.derivedTensor (Profinite.padicIntegersRingObj ℓ E.1) X).obj K).obj M)) ∧
    (∀ (S V : Scheme.{u}) [S.Over (Spec (.of k))] [V.Over (Spec (.of k))]
      [LocallyOfFiniteType (S ↘ Spec (.of k))]
      [QuasiCompact (S ↘ Spec (.of k))] [IsSeparated (S ↘ Spec (.of k))]
      [LocallyOfFiniteType (V ↘ Spec (.of k))]
      [QuasiCompact (V ↘ Spec (.of k))] [IsSeparated (V ↘ Spec (.of k))]
      [IsNoetherian S] [IsNoetherian V] (j : S ⟶ V) (i : V ⟶ X)
      [j.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))]
      [IsOpenImmersion j] [IsClosedImmersion i]
      (L : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (integralCoefficientObject S ℓ E))),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) S L →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X
        ((CondensedRing.moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.1)
          i).obj (((CondensedRing.openImmersionLowerShriek
            (Profinite.padicIntegersRingObj ℓ E.1) j).mapDerivedCategory).obj L))) ∧
    (∀ K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (finiteCoefficientObject X ℓ E)),
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) X K →
      (sInf {P | integralModelGenerator X ℓ E ≤ P ∧ P.IsTriangulated ∧
        P.IsClosedUnderIsomorphisms}) K) ∧
    (∀ K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (qlbarCoefficientObject X ℓ)),
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X K →
      ∃ E' : PadicAlgCl.FiniteIntermediateField ℓ,
        (sInf {P | qlbarModelGenerator X ℓ E' ≤ P ∧ P.IsTriangulated ∧
          P.IsClosedUnderIsomorphisms}) K) ∧
    (∀ (S V : Scheme.{u}) [S.Over (Spec (.of k))] [V.Over (Spec (.of k))]
      [LocallyOfFiniteType (S ↘ Spec (.of k))]
      [QuasiCompact (S ↘ Spec (.of k))] [IsSeparated (S ↘ Spec (.of k))]
      [LocallyOfFiniteType (V ↘ Spec (.of k))]
      [QuasiCompact (V ↘ Spec (.of k))] [IsSeparated (V ↘ Spec (.of k))]
      [IsNoetherian S] [IsNoetherian V] (j : S ⟶ V) (i : V ⟶ X)
      [j.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))]
      [IsOpenImmersion j] [IsClosedImmersion i]
      (L₀ : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (integralCoefficientObject S ℓ E)),
      CondensedRing.LocallyFree (integralCoefficientObject S ℓ E) L₀ →
      integralReductionHasEtaleOrigin X ℓ E π j i L₀) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (localizingClosure_ctf_equals_bc ℓ X
      (Profinite.padicIntegersRingObj ℓ E.1)
      (Or.inr (Or.inr (Or.inl ⟨E, Or.inl ⟨Iso.refl _⟩⟩)))).1.2.2.1
  · exact (integralModelsEmbeddedCompletion ℓ E π hπ X).1
  · intro K
    have hc := (integralModelsEmbeddedCompletion ℓ E π hπ X).2 K
    have hs := integralModelsEmbeddedStacksCriterion ℓ E π hπ X K
    refine ⟨hs, hs.trans ?_⟩
    exact and_congr hc.symm (integralModelsEmbeddedResidueComparison ℓ E π hπ X K)
  · intro Y _ _ _ _ _ f _ K hK
    have h := (CondensedRing.integralModels_operations ℓ E).1 f K hK
    let F := CondensedRing.upperStar (Profinite.padicIntegersRingObj ℓ E.1) f
    let := (constantModelConstructibleFiniteTor_wellDefined
      (Profinite.padicIntegersRingObj ℓ E.1) X).2.1
    exact ObjectProperty.prop_of_iso
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X)
      (F.leftDerivedFunctorIsoMapDerivedCategory.app K).symm h
  · exact (CondensedRing.integralModels_operations ℓ E).2.1 X
  · intro S V _ _ _ _ _ _ _ _ _ _ j i _ _ _ _ L hL
    exact (CondensedRing.integralModels_operations ℓ E).2.2 j i L hL
  · intro K hK
    exact (integral_models_generators k p ℓ hℓp X E π hπ).1 K hK
  · intro K hK
    exact (integral_models_generators k p ℓ hℓp X E π hπ).2.1 K hK
  · intro S V _ _ _ _ _ _ _ _ _ _ j i _ _ _ _ L hL
    exact (integral_models_generators k p ℓ hℓp X E π hπ).2.2 S V j i L hL

end AlgebraicGeometry.ProEtale
