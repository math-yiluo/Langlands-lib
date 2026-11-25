/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.AlgebraicGeometry.Refinement.RefinementCoefficientRealization
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.ConstructibleSheaf.OpenClosed
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientIntrinsicConstructibility
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import Mathlib.Data.Finset.Lattice.Fold
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB

import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import WeilConjectures.AlgebraicGeometry.NilpotentReductionLissity
import WeilConjectures.CategoryTheory.LocallyConstantFiniteTypeModules
import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.NilpotentReductionStep
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.CategoryTheory.Sites.Pretopology
import WeilConjectures.AlgebraicGeometry.ConstantCoefficientLocalModelsComparison
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.AlgebraicGeometry.SiteFiniteFreeTruncationModels
import WeilConjectures.AlgebraicGeometry.SiteLocallyConstantFiniteType
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Category.ModuleCat.Free
import WeilConjectures.AlgebraicGeometry.SiteBoundedTruncationModels
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.SiteBoundedConstantModel
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.AlgebraicGeometry.SiteBoundedConstantGradedModel
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Abelian
import WeilConjectures.AlgebraicGeometry.SiteFiniteConstantExtensionTower
import WeilConjectures.AlgebraicGeometry.FiniteConstantExtensionTower
import WeilConjectures.AlgebraicGeometry.SiteFiniteConstantConeStep
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.AlgebraicGeometry.SiteFiniteLocallyConstantWeakSerre
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.CategoryTheory.Site.SiteModuleSheafConstantRingEquivalenceSupplement
import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantSerre
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.CategoryTheory.FiniteTypeConstantExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import WeilConjectures.CategoryTheory.FiniteTypeRestrictionExact
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.FiniteTypeConstantLocalLinear
import WeilConjectures.CategoryTheory.SiteConstantModuleHomSurjective
import WeilConjectures.Algebra.Homology.SmoothPurity.ConstantLocalModuleHomSupplement
import WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import WeilConjectures.CategoryTheory.Site.SiteConstantModuleUnitSupplement
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.CategoryTheory.SiteConstantModuleOverHom
import WeilConjectures.CategoryTheory.FinitePresentationLocalLift
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.ConstantForget
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.CategoryTheory.FiniteTypeExtensionLocalPresentation
import WeilConjectures.CategoryTheory.ConstantFiniteFreeLocalLift
import WeilConjectures.CategoryTheory.FiniteSectionsEpiLift
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.CategoryTheory.ExtensionCokernelPresentation
import WeilConjectures.Algebra.Homology.SmoothPurity.LocalModuleIsoSupplement
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.RingTheory.Finiteness.Cardinality
import WeilConjectures.CategoryTheory.FiniteTypeRestrictionMapExact
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.LinearAlgebra.StdBasis
import WeilConjectures.AlgebraicGeometry.BoundedTopMorphisms
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.RingTheory.Finiteness.Basic
import WeilConjectures.AlgebraicGeometry.SiteFiniteConstantComplexDescent
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.Additive
import Mathlib.Data.Int.Interval
import WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.RingTheory.RingPseudoCoherent
import WeilConjectures.RingTheory.FiniteFreeResolution
import WeilConjectures.RingTheory.PseudoCoherentOfCohomology
import Mathlib.Algebra.Homology.Single
import WeilConjectures.RingTheory.PseudoCoherentIffAllM
import WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.AlgebraicGeometry.ConstantCoefficientLisseTriangle
import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
import WeilConjectures.AlgebraicGeometry.ConstantCoefficientLisseRestriction
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlat
import WeilConjectures.Algebra.Homology.ChangeOfRingsComplex
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellation
import WeilConjectures.AlgebraicGeometry.LocallyConstantTensor
import WeilConjectures.AlgebraicGeometry.SiteTensorLocalModelComparison
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.Algebra.Homology.SliceTensorNatural
import WeilConjectures.Algebra.Homology.SliceModuleSheafification
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlatLimits
import WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.RingedSliceExtensionPreservesExact
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists
import WeilConjectures.CategoryTheory.RingedSliceExtensionReflectsExact
import Mathlib.CategoryTheory.Sites.LocallyInjective
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import Mathlib.RingTheory.TensorProduct.Finite
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.AlgebraicGeometry.ConstantCoefficientScalarEquivalence
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicLisseFixed
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedTowerLissePropagation

/-! # Common lisse strata for a normalized tower

## References

* Stacks Project and the local-effectivity argument in amplification (c)
* Stacks Project, Tag 094I
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private noncomputable def pullbackScalarExtensionIso
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    pbcDerivedExtend φ ⋙ adicTowerPullback g S ≅
      adicTowerPullback g R ⋙ pbcDerivedExtend ((adicTowerInverseImage g).map φ) := by
  let d := proEtaleRingRestrictionDerivedDirectImage g R S
    ((adicTowerInverseImage g).obj R) ((adicTowerInverseImage g).obj S)
    φ ((adicTowerInverseImage g).map φ) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
  let a₀ := (pbcDerivedScalarAdjunction φ).comp
    (proEtaleRingDerivedAdjunction g S ((adicTowerInverseImage g).obj S) (Iso.refl _))
  let a := a₀.ofNatIsoRight d
  let b := (proEtaleRingDerivedAdjunction g R
    ((adicTowerInverseImage g).obj R) (Iso.refl _)).comp
      (pbcDerivedScalarAdjunction ((adicTowerInverseImage g).map φ))
  exact a.leftAdjointUniq b

private def identityStratification (X : Scheme.{u}) : Stratification X where
  n := 1
  stratum _ := Set.univ
  isLocallyClosed_stratum _ := isOpen_univ.isLocallyClosed
  isConstructible_stratum _ := Topology.IsConstructible.univ
  iUnion_stratum_eq_univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨0, Set.mem_univ x⟩
  pairwise_disjoint_stratum i j hij := (hij (Subsingleton.elim _ _)).elim
  domain _ := X
  immersion _ := 𝟙 X
  range_immersion _ := Set.range_id

private theorem refines_trans {X : Scheme.{u}} {S T U : Stratification X}
    (hST : S.Refines T) (hTU : T.Refines U) : S.Refines U := by
  intro i
  obtain ⟨j, hj⟩ := hST i
  obtain ⟨k, hk⟩ := hTU j
  exact ⟨k, hj.trans hk⟩

private theorem common_finite_stratification {X : Scheme.{u}}
    (s : Finset (Stratification X)) :
    ∃ T : Stratification X, ∀ S ∈ s, T.Refines S := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨identityStratification X, by simp⟩
  | @insert S s hS ih =>
    obtain ⟨T, hT⟩ := ih
    refine ⟨T.inter S, ?_⟩
    intro U hU
    rcases Finset.mem_insert.mp hU with rfl | hU
    · exact T.inter_refines_right U
    · exact refines_trans (T.inter_refines_left S) (hT U hU)

private theorem common_constructible_stratification {X : Scheme.{u}}
    {I : Type*} [Finite I] (B : Type (u + 1)) [CommRing B]
    (F : I → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    (hF : ∀ i, IsConstructibleSheaf (F i)) :
    ∃ S : Stratification X, ∀ (i : I) (j : Fin S.n),
      IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} B) (S.immersion j)).obj (F i)) := by
  classical
  let := Fintype.ofFinite I
  choose S hS using fun i ↦ (hF i).exists_stratification
  obtain ⟨T, hT⟩ := common_finite_stratification (Finset.univ.image S)
  refine ⟨T, fun i j ↦ ?_⟩
  exact (hT (S i) (by simp)).isFiniteLocallyConstantSheaf_upperStar (F i) (hS i) j

private theorem common_bounded_constructible_stratification {X : Scheme.{u}}
    (B : Type (u + 1)) [CommRing B]
    (F : ℤ → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    (a b : ℤ) (hF : ∀ q, a ≤ q ∧ q ≤ b → IsConstructibleSheaf (F q))
    (hzero : ∀ q, q < a ∨ b < q → IsZero (F q)) :
    ∃ S : Stratification X, ∀ (i : Fin S.n) (q : ℤ),
      IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} B) (S.immersion i)).obj (F q)) := by
  classical
  let I := {q : ℤ // q ∈ Finset.Icc a b}
  obtain ⟨S, hS⟩ := common_constructible_stratification B
    (fun q : I ↦ F q.1) (fun q ↦ hF q.1 (Finset.mem_Icc.mp q.2))
  refine ⟨S, fun i q ↦ ?_⟩
  by_cases hq : q ∈ Finset.Icc a b
  · exact hS ⟨q, hq⟩ i
  · apply IsFiniteLocallyConstantSheaf.of_isZero
    apply (Etale.upperStar (ModuleCat.{u + 1} B) (S.immersion i)).map_isZero
    exact hzero q (by simpa only [Finset.mem_Icc, not_and_or, not_le] using hq)

private theorem common_proEtale_stratification {X : Scheme.{u}}
    (B : Type (u + 1)) [CommRing B] [Finite B]
    (F : ℤ → Sheaf (ProEt.topology X) (ModuleCat.{u + 1} B))
    (a b : ℤ) (hF : ∀ q, ProEtale.IsConstructible B (F q))
    (hzero : ∀ q, q < a ∨ b < q → IsZero (F q)) :
    ∃ S : Stratification X, ∀ (i : Fin S.n) (q : ℤ),
      ProEtale.IsFiniteLocallyConstant B
        ((ProEtale.upperStar (ModuleCat.{u + 1} B) (S.immersion i)).obj (F q)) := by
  classical
  choose G hG e using fun q ↦
    ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj B (hF q)
  have hGzero (q : ℤ) (hq : q < a ∨ b < q) : IsZero (G q) := by
    apply IsZero.of_full_of_faithful_of_isZero
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X)
    exact (hzero q hq).of_iso (e q).some
  obtain ⟨S, hS⟩ := common_bounded_constructible_stratification B G a b
    (fun q _ ↦ hG q) hGzero
  refine ⟨S, fun i q ↦ ?_⟩
  have := hS i q
  exact ProEtale.isFiniteLocallyConstant_of_iso
    (((ProEtale.comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} B) (S.immersion i)).app (G q)).symm ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} B) (S.immersion i)).mapIso (e q).some)
    (ProEtale.isFiniteLocallyConstant_comparisonUpperStar_obj _)

namespace NormalizedTowerCoefficients

set_option backward.isDefEq.respectTransparency.types false in

private theorem constantRingInverseImage_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] :
    IsIso (proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of A)) := by
  -- Compare the two left adjoints to sections at the base-changed terminal object.
  let D := CommRingCat.{u + 1}
  let T : Y.ProEt := ProEt.mk (𝟙 Y)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ Y
  let hGT : IsTerminal ((proEtaleBaseChange f).obj T) :=
    hT.isTerminalObj (proEtaleBaseChange f)
  let eR : proEtaleSheafDirectImage f D ⋙
      (sheafSections (ProEt.topology Y) D).obj (Opposite.op T) ≅
        (sheafSections (ProEt.topology X) D).obj (Opposite.op ((proEtaleBaseChange f).obj T)) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
  let adj₁ := ((constantSheafAdj (ProEt.topology Y) D hT).comp
    (proEtaleSheafAdjunction f D)).ofNatIsoRight eR
  let adj₂ := constantSheafAdj (ProEt.topology X) D hGT
  let e := adj₁.leftAdjointUniq adj₂
  -- Identify the specified map by its transpose, including its constant-section normalization.
  have he : proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of A) =
      e.hom.app (CommRingCat.of A) := by
    apply (adj₁.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    simp only [adj₁, Adjunction.homEquiv_ofNatIsoRight_apply,
      Adjunction.comp_homEquiv]
    unfold proEtaleConstantInverseImageMap
    rw [← Adjunction.homEquiv_symm_apply]
    dsimp only [D, proEtaleSheafDirectImage, ProEtale.lowerStar,
      proEtaleConstantRing, Functor.comp_obj] at *
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply, eR,
      NatIso.ofComponents_hom_app, Iso.refl_hom]
    change (constantSheafAdj (ProEt.topology Y) D hT).homEquiv _ _
      (proEtaleConstantDirectImageMap f D (CommRingCat.of A)) =
        adj₂.unit.app _
    unfold proEtaleConstantDirectImageMap
    rw [constantSheafAdj, Adjunction.comp_homEquiv]
    change (constantPresheafAdj D hT).homEquiv _ _
      ((sheafificationAdjunction (ProEt.topology Y) D).homEquiv _ _
        (((sheafificationAdjunction (ProEt.topology Y) D).homEquiv _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    simp only [adj₂, constantSheafAdj, Adjunction.comp_unit_app,
      constantPresheafAdj_unit_app, Category.id_comp, sheafificationAdjunction_unit_app]
    rfl
  rw [he]
  infer_instance

variable (T : Scheme.{u}) (B : Type (u + 1)) [CommRing B]

private abbrev wideConstantModuleScalarUnit := adicLisseConstantUnit T B

private abbrev wideConstantModuleRestriction (T : Scheme.{u})
    (B : Type (u + 1)) [CommRing B] :=
  ConstantScalarComparison.restriction (ProEt.topology T) B (adicLisseRing T B)
    (wideConstantModuleScalarUnit T B)

private instance wideConstantModuleRestriction_additive
    (Z : Scheme.{u}) (D : Type (u + 1)) [CommRing D] :
    (wideConstantModuleRestriction Z D).Additive where
  map_add := by intros; ext U x; rfl

private noncomputable def constantModulePresheaf :
    (T.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (B)) ⥤
      PresheafOfModules.{u + 1}
        ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (B))) where
  obj F :=
    { obj := F.obj
      map f := F.map f
      map_id U := by ext x; exact ConcreteCategory.congr_hom (F.map_id U) x
      map_comp f g := by ext x; exact ConcreteCategory.congr_hom (F.map_comp f g) x }
  map φ :=
    { app := φ.app
      naturality f := by ext x; exact ConcreteCategory.congr_hom (φ.naturality f) x }

private noncomputable def constantModuleFullyFaithful :
    (constantModulePresheaf T B).FullyFaithful where
  preimage φ :=
    { app := φ.app
      naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (φ.naturality f) x }
  map_preimage φ := by ext U x; rfl
  preimage_map φ := by ext U x; rfl

private noncomputable instance : (constantModulePresheaf T B).Full :=
  (constantModuleFullyFaithful T B).full

private noncomputable instance : (constantModulePresheaf T B).Faithful :=
  (constantModuleFullyFaithful T B).faithful

private noncomputable def moduleEmbedding :=
  sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} (B)) ⋙
    constantModulePresheaf T B

private noncomputable instance : (moduleEmbedding T B).Full :=
  inferInstanceAs (sheafToPresheaf (ProEt.topology T)
    (ModuleCat.{u + 1} (B)) ⋙ constantModulePresheaf T B).Full

private noncomputable instance : (moduleEmbedding T B).Faithful :=
  inferInstanceAs (sheafToPresheaf (ProEt.topology T)
    (ModuleCat.{u + 1} (B)) ⋙ constantModulePresheaf T B).Faithful

private noncomputable instance restriction_full : (wideConstantModuleRestriction T B).Full :=
  (ConstantScalarComparison.restrictionFullyFaithful (ProEt.topology T) B
    (adicLisseRing T B) (wideConstantModuleScalarUnit T B)).full

private noncomputable instance restriction_faithful :
    (wideConstantModuleRestriction T B).Faithful :=
  (ConstantScalarComparison.restrictionFullyFaithful (ProEt.topology T) B
    (adicLisseRing T B) (wideConstantModuleScalarUnit T B)).faithful

private noncomputable instance restriction_essSurj :
    (wideConstantModuleRestriction T B).EssSurj where
  mem_essImage F := by
    let P := (moduleEmbedding T B).obj F
    let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
      (wideConstantModuleScalarUnit T B)
    have hη : IsIso (adj.unit.app P) := by
      rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
      change IsIso (toSheafify (ProEt.topology T) P.presheaf)
      exact isIso_toSheafify (ProEt.topology T)
        ((sheafCompose (ProEt.topology T)
          (forget₂ (ModuleCat.{u + 1} (B))
            AddCommGrpCat.{u + 1})).obj F).property
    refine ⟨(PresheafOfModules.sheafification.{u + 1}
      (wideConstantModuleScalarUnit T B)).obj P, ⟨?_⟩⟩
    exact (Functor.FullyFaithful.ofFullyFaithful (moduleEmbedding T B)).preimageIso
      (asIso (adj.unit.app P)).symm

private theorem wideConstantModuleRestriction_isEquivalence :
    (wideConstantModuleRestriction T B).IsEquivalence := by
  exact {}

private noncomputable def wideConstantModuleEncoding :
    pbcModules T (adicLisseConstantRing T B) ≌
      Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (B)) :=
  haveI := wideConstantModuleRestriction_isEquivalence T B
  (wideConstantModuleRestriction T B).asEquivalence

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (B : Type (u + 1)) [CommRing B]

private noncomputable def coefficientIso
    [IsIso (proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of B))] :=
  asIso (proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of B))

private theorem coefficient_adjunct
    [IsIso (proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of B))] :
    proEtaleRingDirectImageMap f (adicLisseConstantRing Y B) (adicLisseConstantRing X B)
      (coefficientIso f B) =
      proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of B) := by
  let adj := proEtaleSheafAdjunction f CommRingCat.{u + 1}
  change adj.unit.app _ ≫ (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
      (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of B)) ≫
      adj.counit.app _) = _
  exact (adj.homEquiv _ _).apply_symm_apply
    (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of B))

private theorem constant_sections :
    toSheafify (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (B))) ≫
      (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of B)).hom =
    Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (B)))) := by
  exact ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    _ _).apply_symm_apply _

private noncomputable def directImageComparison
    [IsIso (proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of B))] :
    proEtaleRingModuleDirectImage f (adicLisseConstantRing Y B) (adicLisseConstantRing X B)
        (coefficientIso f B) ⋙ wideConstantModuleRestriction Y B ≅
      wideConstantModuleRestriction X B ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} (B)) f := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ?_) ?_)) ?_
  · let P := (((proEtaleRingModuleDirectImage f (adicLisseConstantRing Y B)
        (adicLisseConstantRing X B) (coefficientIso f B) ⋙
          wideConstantModuleRestriction Y B).obj M).obj.obj U)
    let Q := (((wideConstantModuleRestriction X B ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} (B)) f).obj M).obj.obj U)
    change P ≅ Q
    refine (show (P : Type (u + 1)) ≃ₗ[B] Q from
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun b m ↦ ?_ }).toModuleIso
    change ((proEtaleRingDirectImageMap f (adicLisseConstantRing Y B)
        (adicLisseConstantRing X B) (coefficientIso f B)).hom.app U).hom
          (((wideConstantModuleScalarUnit Y B).app U).hom b) •
          (show M.val.obj ((proEtaleBaseChange f).op.obj U) from m) =
      (((wideConstantModuleScalarUnit X B).app ((proEtaleBaseChange f).op.obj U)).hom b) •
          (show M.val.obj ((proEtaleBaseChange f).op.obj U) from m)
    rw [coefficient_adjunct]
    exact congrArg (fun r ↦ r •
      (show M.val.obj ((proEtaleBaseChange f).op.obj U) from m))
      (ConcreteCategory.congr_hom (congr_app (constant_sections f B) U) b)
  · intro U V a
    ext m
    rfl
  · intro M N a
    ext U m
    rfl

attribute [local irreducible] directImageComparison

private noncomputable def wideConstantModuleRestriction_pullback_iso
    [IsIso (proEtaleConstantInverseImageMap f CommRingCat.{u + 1} (CommRingCat.of B))]
:
    proEtaleRingModulePullback f (adicLisseConstantRing Y B)
      (adicLisseConstantRing X B) (coefficientIso f B) ⋙ wideConstantModuleRestriction X B ≅
    wideConstantModuleRestriction Y B ⋙ ProEtale.upperStar (ModuleCat.{u + 1} B) f := by
  let EX := wideConstantModuleEncoding X B
  let EY := wideConstantModuleEncoding Y B
  let L := ProEtale.upperStar (ModuleCat.{u + 1} (B)) f
  let R := ProEtale.lowerStar (ModuleCat.{u + 1} (B)) f
  let adj := EY.toAdjunction.comp
    ((ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (B)) f).comp EX.symm.toAdjunction)
  let eR : EX.functor ⋙ R ⋙ EY.inverse ≅
      proEtaleRingModuleDirectImage f (adicLisseConstantRing Y B) (adicLisseConstantRing X B)
        (coefficientIso f B) :=
    (Functor.isoWhiskerRight (directImageComparison f B).symm EY.inverse) ≪≫
      Functor.isoWhiskerLeft _ EY.unitIso.symm
  let adj' := adj.ofNatIsoRight eR
  let e := (proEtaleRingModuleAdjunction f (adicLisseConstantRing Y B)
    (adicLisseConstantRing X B) (coefficientIso f B)).leftAdjointUniq adj'
  exact Functor.isoWhiskerRight e EX.functor ≪≫
    Functor.isoWhiskerLeft (EY.functor ⋙ L) EX.counitIso

attribute [local irreducible] wideConstantModuleRestriction_pullback_iso

private noncomputable def constantRestrictionIso (Z : Scheme.{u})
    (D : Type (u + 1)) [CommRing D] (M : ModuleCat.{u + 1} D) :
    (constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} D)).obj M ≅
      (wideConstantModuleRestriction Z D).obj ((adicLisseConstantModules Z D).obj M) := by
  have h := ConstantScalarComparison.constantComparisonHom_isIso
    (ProEt.topology Z) D (adicLisseRing Z D) (wideConstantModuleScalarUnit Z D) M
  exact asIso (ConstantScalarComparison.constantComparisonHom
    (ProEt.topology Z) D (adicLisseRing Z D) (wideConstantModuleScalarUnit Z D) M)

attribute [local irreducible] constantRestrictionIso

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def inverseImageCoefficientIso
    {Z W : Scheme.{u}} (g : W ⟶ Z) (D : Type (u + 1)) [CommRing D] :
    haveI := NormalizedTowerCoefficients.constantRingInverseImage_isIso g D
    proEtaleModuleInverseImage g (adicLisseConstantRing Z D) ⋙
      pbcRestrict (coefficientIso g D).inv ≅
    proEtaleRingModulePullback g (adicLisseConstantRing Z D)
      (adicLisseConstantRing W D) (coefficientIso g D) := by
  have := constantRingInverseImage_isIso g D
  let c := coefficientIso g D
  let E := proEtaleScalarEquivalence W ((adicLisseForget W).mapIso c)
  let j := (proEtaleRingExtensionAdjunction g (adicLisseConstantRing Z D)
    (adicLisseConstantRing W D) c).leftAdjointUniq E.symm.toAdjunction
  exact (Functor.isoWhiskerLeft
    (proEtaleModuleInverseImage g (adicLisseConstantRing Z D)) j).symm

attribute [local irreducible] inverseImageCoefficientIso

private noncomputable def fixedConstantPullbackIso
    {Z W : Scheme.{u}} (g : W ⟶ Z) (D : Type (u + 1)) [CommRing D]
    (M : ModuleCat.{u + 1} D) :
    (ProEtale.upperStar (ModuleCat.{u + 1} D) g).obj
      ((constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} D)).obj M) ≅
    (constantSheaf (ProEt.topology W) (ModuleCat.{u + 1} D)).obj M := by
  let T : Z.ProEt := ProEt.mk (𝟙 Z)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ Z
  let hGT := hT.isTerminalObj (proEtaleBaseChange g)
  let eR : ProEtale.lowerStar (ModuleCat.{u + 1} D) g ⋙
      (sheafSections (ProEt.topology Z) (ModuleCat.{u + 1} D)).obj (Opposite.op T) ≅
      (sheafSections (ProEt.topology W) (ModuleCat.{u + 1} D)).obj
        (Opposite.op ((proEtaleBaseChange g).obj T)) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
  let adj := ((constantSheafAdj (ProEt.topology Z) (ModuleCat.{u + 1} D) hT).comp
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} D) g)).ofNatIsoRight eR
  exact (adj.leftAdjointUniq
    (constantSheafAdj (ProEt.topology W) (ModuleCat.{u + 1} D) hGT)).app M

attribute [local irreducible] fixedConstantPullbackIso


private def restrictCancelIso {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (α : R ⟶ S) (β : S ⟶ R)
    (h : α ≫ β = 𝟙 R) :
    SheafOfModules.restrictScalars β ⋙ SheafOfModules.restrictScalars α ≅
      𝟭 (SheafOfModules.{u + 1} R) := by
  have hU (U : Cᵒᵖ) : (β.hom.app U).hom.comp (α.hom.app U).hom =
      RingHom.id (R.obj.obj U) :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k : R ⟶ R ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
        (RingHom.id (R.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
      (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U)) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

attribute [local irreducible] restrictCancelIso

private abbrev coefficientEquivalence {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (e : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R :=
  CategoryTheory.Equivalence.mk (SheafOfModules.restrictScalars e.hom)
    (SheafOfModules.restrictScalars e.inv)
    (restrictCancelIso e.inv e.hom e.inv_hom_id).symm
    (restrictCancelIso e.hom e.inv e.hom_inv_id)

private noncomputable def restrictionOverIso
    {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (α : R ⟶ S) (U : C) :
    SheafOfModules.restrictScalars α ⋙ SheafOfModules.overFunctor R U ≅
    SheafOfModules.overFunctor S U ⋙
      SheafOfModules.restrictScalars ((J.overPullback RingCat.{u + 1} U).map α) := by
  refine NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) ?_)) ?_
  · intros
    ext x
    rfl
  · intros
    ext V x
    rfl


private abbrev nativeSieveFiniteLisse := NormalizedNativeSieveFiniteLisse

private noncomputable def nativeOverRestrictionIso
    (Z : Scheme.{u}) (D : Type (u + 1)) [CommRing D] (U : Z.ProEt)
    (F : pbcModules Z (adicLisseConstantRing Z D)) :
    ((wideConstantModuleRestriction Z D).obj F).over U ≅
      (ConstantScalarComparison.restriction ((ProEt.topology Z).over U) D
        ((adicLisseRing Z D).over U)
        (Functor.whiskerLeft (Over.forget U).op (wideConstantModuleScalarUnit Z D))).obj
          (F.over U) := by
  exact ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))

private theorem native_over_iso_of_fixed
    (Z : Scheme.{u}) (D : Type (u + 1)) [CommRing D] (U : Z.ProEt)
    (F G : pbcModules Z (adicLisseConstantRing Z D))
    (e : ((wideConstantModuleRestriction Z D).obj F).over U ≅
      ((wideConstantModuleRestriction Z D).obj G).over U) :
    Nonempty (F.over U ≅ G.over U) := by
  let a := Functor.whiskerLeft (Over.forget U).op (wideConstantModuleScalarUnit Z D)
  have : Presheaf.IsLocallySurjective ((ProEt.topology Z).over U) a :=
    Presheaf.isLocallySurjective_whisker ((ProEt.topology Z).over U)
      (ProEt.topology Z) (Over.forget U) (wideConstantModuleScalarUnit Z D)
  exact ⟨(ConstantScalarComparison.restrictionFullyFaithful
    ((ProEt.topology Z).over U) D ((adicLisseRing Z D).over U) a).preimageIso
      ((nativeOverRestrictionIso Z D U F).symm ≪≫ e ≪≫
        nativeOverRestrictionIso Z D U G)⟩

private theorem nativeSieveFiniteLisse_of_fixed
    (Z : Scheme.{u}) (D : Type (u + 1)) [CommRing D] [Finite D]
    (F : pbcModules Z (adicLisseConstantRing Z D))
    (h : ProEtale.IsFiniteLocallyConstant D ((wideConstantModuleRestriction Z D).obj F)) :
    nativeSieveFiniteLisse Z D F := by
  obtain ⟨I, W, g, hg, hmodels⟩ := h
  have hw : ∀ i, WeaklyEtale (g i) := by
    have hw := hg.2
    rw [Scheme.ofArrows_mem_precoverage_iff] at hw
    exact hw.2
  let U : I → Z.ProEt := fun i ↦ @ProEt.mk _ (W i) (g i) (hw i)
  let T : Z.ProEt := ProEt.mk (𝟙 Z)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ Z
  let f : ∀ i, U i ⟶ T := fun i ↦ MorphismProperty.Over.homMk (g i)
    (by exact Category.comp_id _)
  let P := Presieve.ofArrows U f
  have hP : P ∈ ProEt.precoverage Z T := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    exact hg
  let S := Sieve.generate P
  have hS : S ∈ ProEt.topology Z T :=
    ProEt.mem_topology_iff.mpr ⟨P, hP, Sieve.le_generate P⟩
  have he (i : I) : ∃ M : ModuleCat.{u + 1} D, Finite M ∧
      Nonempty (F.over (U i) ≅ ((adicLisseConstantModules Z D).obj M).over (U i)) := by
    obtain ⟨M, hM, ⟨e⟩⟩ := hmodels i
    refine ⟨M, Module.finite_of_finite D, ?_⟩
    have : (ProEt.sliceEquiv Z (U i)).inverse.IsDenseSubsite
        (ProEt.topology (U i).left) ((ProEt.topology Z).over (U i)) :=
      ProEt.sliceDense Z (U i)
    let E := (ProEt.sliceEquiv Z (U i)).sheafCongr
      ((ProEt.topology Z).over (U i)) (ProEt.topology (U i).left)
      (ModuleCat.{u + 1} D)
    let G := (wideConstantModuleRestriction Z D).obj F
    let r : E.functor.obj (G.over (U i)) ≅
        (ProEtale.localizationRestriction (ModuleCat.{u + 1} D)
          (U i).hom (U i).prop).obj G :=
      ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
    let c := ((ProEt.sliceEquiv Z (U i)).constantSheafSheafCongrIso
      ((ProEt.topology Z).over (U i)) (ProEt.topology (U i).left)
      (ModuleCat.{u + 1} D) (Over.mkIdTerminal (X := U i))).app M
    let co := ((ProEt.topology Z).overPullbackConstantSheafIso
      (ModuleCat.{u + 1} D) (U i)).app M
    let j : G.over (U i) ≅
        ((constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} D)).obj M).over (U i) :=
      E.fullyFaithfulFunctor.preimageIso
        (r ≪≫ (ProEtale.upperStarIsoLocalizationRestriction
          (ModuleCat.{u + 1} D) (U i).hom (U i).prop).symm.app G ≪≫ e ≪≫
          (E.functor.mapIso co ≪≫ c).symm)
    exact native_over_iso_of_fixed Z D (U i) F _
      (j ≪≫ ((ProEt.topology Z).overPullback (ModuleCat.{u + 1} D) (U i)).mapIso
        (constantRestrictionIso Z D M))
  refine ⟨S.pullback (hT.from (⊤_ Z.ProEt)),
    (ProEt.topology Z).pullback_stable _ hS, fun V a ha ↦ ?_⟩
  obtain ⟨_, k, _, ⟨i⟩, _⟩ := ha
  obtain ⟨M, hM, ⟨e⟩⟩ := he i
  refine ⟨M, hM, ⟨?_⟩⟩
  exact ((SheafOfModules.overFunctorMap _ k).app F).symm ≪≫
    (SheafOfModules.overMap _ k).mapIso e ≪≫
    (SheafOfModules.overFunctorMap _ k).app ((adicLisseConstantModules Z D).obj M)

private theorem native_constructible_fixed
    (Z : Scheme.{u}) [IsNoetherian Z] (D : Type (u + 1)) [CommRing D] [Finite D]
    (F : pbcModules Z (adicLisseConstantRing Z D))
    (h : IsConstructibleProEtaleCoefficientModuleSheaf Z D F) :
    ProEtale.IsConstructible D ((wideConstantModuleRestriction Z D).obj F) := by
  obtain ⟨S, _, _, hs⟩ := h
  refine ⟨S, fun i ↦ ?_⟩
  let g := S.immersion i
  have := constantRingInverseImage_isIso g D
  let c := coefficientIso g D
  let P := (proEtaleModuleInverseImage g (adicLisseConstantRing Z D)).obj F
  let E := wideConstantModuleRestriction (S.domain i) D
  let j : E.obj ((pbcRestrict c.inv).obj P) ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} D) g).obj
        ((wideConstantModuleRestriction Z D).obj F) :=
    E.mapIso ((inverseImageCoefficientIso g D).app F) ≪≫
      (wideConstantModuleRestriction_pullback_iso g D).app F
  let e : (underlying (S.domain i)
      ((adicTowerInverseImage g).obj (adicLisseConstantRing Z D))).obj P ≅
      (sheafCompose (ProEt.topology (S.domain i))
        (CategoryTheory.forget (ModuleCat.{u + 1} D))).obj (E.obj
          ((pbcRestrict c.inv).obj P)) :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  exact relative_lisse_fixed g D P _
    (e ≪≫ (sheafCompose (ProEt.topology (S.domain i))
      (CategoryTheory.forget (ModuleCat.{u + 1} D))).mapIso j) (hs i)

private theorem native_common_strata
    (Z : Scheme.{u}) [IsNoetherian Z] (D : Type (u + 1)) [CommRing D] [Finite D]
    (F : ℤ → pbcModules Z (adicLisseConstantRing Z D))
    (a b : ℤ)
    (hconstructible : ∀ q : ℤ, IsConstructibleProEtaleCoefficientModuleSheaf Z D (F q))
    (hbounded : ∀ q : ℤ, (q < a ∨ b < q) → IsZero (F q)) :
    ∃ S : Stratification Z, ∀ (i : Fin S.n) (q : ℤ),
      haveI := NormalizedTowerCoefficients.constantRingInverseImage_isIso (S.immersion i) D
      nativeSieveFiniteLisse (S.domain i) D
        ((proEtaleRingModulePullback (S.immersion i) (adicLisseConstantRing Z D)
          (adicLisseConstantRing (S.domain i) D) (coefficientIso (S.immersion i) D)).obj
            (F q)) := by
  let E := wideConstantModuleRestriction Z D
  obtain ⟨S, hS⟩ := common_proEtale_stratification D (fun q ↦ E.obj (F q)) a b
    (fun q ↦ native_constructible_fixed Z D (F q) (hconstructible q))
    (fun q hq ↦ E.map_isZero (hbounded q hq))
  refine ⟨S, fun i q ↦ ?_⟩
  have := constantRingInverseImage_isIso (S.immersion i) D
  apply nativeSieveFiniteLisse_of_fixed
  exact ProEtale.isFiniteLocallyConstant_of_iso
    ((wideConstantModuleRestriction_pullback_iso (S.immersion i) D).app (F q)).symm
    (hS i q)

end NormalizedTowerCoefficients

/-- A stratification for the first quotient controls lissity at every normalized level.
No common completed complex or normalization-compatible trivialization is asserted here. -/
theorem normalizedTower_common_lisse_strata
    (X : Scheme.{u}) [IsNoetherian X] {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (hconstructible : ∀ q : ℤ,
      @IsConstructibleProEtaleCoefficientModuleSheaf X (A ⧸ d.ideal ^ (0 + 1)) _
        (d.quotientFinite 0)
        ((pbcRestrict (pbcLevelConstantComparison X d 0).hom).obj
          ((DerivedCategory.homologyFunctor _ q).obj (M.level 0))))
    (a b : ℤ) (hab : a ≤ b)
    (hbounded : ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (M.level n))) :
    ∃ S : Stratification X, ∀ (i : Fin S.n) (n : ℕ) (q : ℤ),
      IsRelativelyFiniteLisseModule (S.immersion i) (A ⧸ d.ideal ^ (n + 1))
        ((pbcRestrict ((adicTowerInverseImage (S.immersion i)).map
          (pbcLevelConstantComparison X d n).hom)).obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((adicTowerPullback (S.immersion i)
                ((pbcAdicRings X d).obj (op n))).obj (M.level n)))) := by
  let D : Type (u + 1) := A ⧸ d.ideal ^ (0 + 1)
  let F : ℤ → pbcModules X (adicLisseConstantRing X D) := fun q ↦
    (pbcRestrict (pbcLevelConstantComparison X d 0).hom).obj
      ((DerivedCategory.homologyFunctor _ q).obj (M.level 0))
  have hF : ∀ q, IsConstructibleProEtaleCoefficientModuleSheaf X D (F q) := by
    intro q
    simpa only [F, D] using hconstructible q
  have hzero : ∀ q, q < a ∨ b < q → IsZero (F q) := by
    intro q hq
    exact (pbcRestrict (pbcLevelConstantComparison X d 0).hom).map_isZero
      (hbounded 0 q hq)
  obtain ⟨S, hS⟩ := NormalizedTowerCoefficients.native_common_strata X D (fun q ↦ F q) a b
    (fun q ↦ hF q) hzero
  refine ⟨S, ?_⟩
  apply normalizedTower_lisse_of_native_strata X d M S a b hab hbounded
  intro i q
  haveI := NormalizedTowerCoefficients.constantRingInverseImage_isIso (S.immersion i) D
  refine ⟨NormalizedTowerCoefficients.coefficientIso (S.immersion i) D, ?_⟩
  simpa only [NormalizedNativeSieveFiniteLisse, F, D] using hS i q

end AlgebraicGeometry.Scheme
