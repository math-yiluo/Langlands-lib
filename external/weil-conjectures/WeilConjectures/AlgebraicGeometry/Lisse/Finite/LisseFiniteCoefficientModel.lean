/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import all Mathlib.Algebra.Field.ULift
import all Mathlib.CategoryTheory.Sites.EpiMono
import all WeilConjectures.ConstructibleSheaf.Refinement
import all WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import all WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.Topology.NoetherianSpace
import all WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Topology.Category.Profinite.AsLimit
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all Mathlib.Topology.Category.Profinite.CofilteredLimit
import all Mathlib.Topology.Connected.TotallyDisconnected
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import all WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Category.Ring.Basic
import all WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import all Mathlib.AlgebraicGeometry.Limits
import all WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import all WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import all WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import all Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import all WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import all WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import all WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import all WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import all WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Topology.Algebra.Valued.NormedValued
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Topology.ContinuousMap.Compact
import all Mathlib.NumberTheory.Padics.ProperSpace
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all Mathlib.CategoryTheory.Abelian.ShortExact
import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import all Mathlib.Data.Matrix.Basic
import all WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all Mathlib.Algebra.Category.ModuleCat.Kernels
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import all Mathlib.AlgebraicGeometry.Morphisms.Flat
import all Mathlib.Topology.LocallyConstant.Basic
import all Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import all WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import all Mathlib.Logic.Equiv.Set
import all Mathlib.Data.Fintype.Basic
import all Mathlib.Topology.ContinuousMap.Algebra
import all Mathlib.Analysis.Normed.Field.Lemmas
import all Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import all WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import all Mathlib.LinearAlgebra.Matrix.ToLin
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import all WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import all WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import all WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import all WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import all WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import all WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import all WeilConjectures.CategoryTheory.ModuleObjects.Free
import all WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import all WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
import all WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import all WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import all WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import all Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all Mathlib.CategoryTheory.ObjectProperty.Extensions
import all Mathlib.CategoryTheory.ObjectProperty.Kernels
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import all WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import all WeilConjectures.AlgebraicGeometry.CondensedFinitePresentationMatrices
import all WeilConjectures.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteFinitePresentationInternalHomColimit
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import all WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomOver
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteGlobalPresentationInternalHomColimit
import all WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
import all WeilConjectures.Mathlib.CategoryTheory.Preadditive.Opposite
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.AlgebraicGeometry.CondensedLocalModelGluing
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalSubmoduleGluing
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalSubmoduleGluingData
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalSubsheafGluing
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalSubobjectKernel
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalSubobjectKernelEffective
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalQuotientVanishing
import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.CondensedFiniteLocalSubmodules
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFamilyHomDescent
import WeilConjectures.AlgebraicGeometry.CondensedLocalCoefficientAdjoints
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexDiagram
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedDerivedTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SplitCoefficientDerivedFaithfulSupplement
import WeilConjectures.AlgebraicGeometry.CondensedOverlapFactorTranspose
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexColimit
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.AlgebraicGeometry.CondensedFpHomStage
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-! # Finite coefficient models for lisse objects
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private lemma finite_affine_free_cover
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (h : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M)) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
      Finite U.I₀ ∧ (∀ i, IsAffine (U.X i)) ∧
      ∀ i, Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj R)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj M) := by
  obtain ⟨U, hU⟩ := h
  obtain ⟨V, q, hfin, ho⟩ := QuasiCompactCover.exists_hom U.forgetQc
  have : Finite V.cover.I₀ := hfin
  have (i : V.cover.I₀) : QuasiCompact (V.cover.f i) := by infer_instance
  let W := Scheme.Cover.ofQuasiCompactCover V.cover
  refine ⟨W, hfin, fun i ↦ ?_, fun i ↦ ?_⟩
  · change IsAffine (Spec (V.X i))
    infer_instance
  · have hi := (free_pullback_comp_iff (q.h₀ i) (U.f (q.s₀ i)) M).mpr
      (free_pullback (q.h₀ i) (hU (q.s₀ i)))
    have hw : q.h₀ i ≫ U.f (q.s₀ i) = W.f i := q.w₀ i
    rw [hw] at hi
    exact hi

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- A lisse module over the algebraic closure admits a lisse finite-field model. -/
theorem exists_lisse_finiteCoefficient_model [CompactSpace X] [QuasiSeparatedSpace X]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))
    (hL : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) L) :
    ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (L_E : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (padicSubfieldRingObj X ℓ E)),
      IsLisseCoefficientModule (Profinite.continuousMapRingObj E) L_E ∧
        Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj L_E ≅ L) := by
  classical
  let B := upperStar Ab.{u + 1} (𝟙 X)
  let R := padicAlgClRingObj X ℓ
  let M := (B.mapMod R).obj L
  obtain ⟨U₀, hU₀⟩ := hL
  have hraw : ∀ i, Mod.IsFree ((upperStar Ab.{u + 1} (U₀.f i)).obj R)
      (((upperStar Ab.{u + 1} (U₀.f i)).mapMod R).obj L) := by
    intro i
    let φ := condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) (U₀.f i)
    apply free_of_comap (inv φ)
    exact free_of_iso (hU₀ i) ((Mod.extendScalarsIsoComapInv φ).app _)
  have hM : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj (B.obj R))
        (((upperStar Ab.{u + 1} (U.f i)).mapMod (B.obj R)).obj M) := by
    refine ⟨U₀, fun i ↦ ?_⟩
    apply (free_pullback_comp_iff (U₀.f i) (𝟙 X) L).mp
    rw [Category.comp_id]
    exact hraw i
  obtain ⟨U, hfinite, haffine, hU⟩ := finite_affine_free_cover (B.obj R) M hM
  choose n en using hU
  let E := Padic.finiteCoefficientBase ℓ (PadicAlgCl ℓ)
  let N i := Mod.finiteFree ((upperStar Ab.{u + 1} (U.f i)).obj
    (B.obj (padicSubfieldRingObj X ℓ E))) (n i)
  have hN : ∀ i, Mod.IsFinitelyPresented _ (N i) :=
    fun i ↦ fp_of_free ⟨n i, ⟨Iso.refl _⟩⟩
  have eN (i : U.I₀) : Nonempty ((Mod.extendScalars
      ((upperStar Ab.{u + 1} (U.f i)).map
        (B.map (padicSubfieldRingObjToPadicAlgCl X ℓ E)))).obj (N i) ≅
      ((upperStar Ab.{u + 1} (U.f i)).mapMod (B.obj R)).obj M) := by
    obtain ⟨ei⟩ := en i
    exact ⟨extended_free_iso _ _ _ (n i) ≪≫ ei.symm⟩
  obtain ⟨F, hEF, P, eP, ⟨eM⟩⟩ := exists_finiteCoefficient_gluing_of_local_models
    X X (𝟙 X) ℓ M E U hfinite haffine N hN eN
  let r := condensedPullbackHom (Profinite.continuousMapRingObj F) (𝟙 X)
  let s := condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) (𝟙 X)
  let a := padicSubfieldRingObjToPadicAlgCl X ℓ F
  let Q := (Mod.extendScalars r).obj P
  have hP : ∀ i, Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj
      (B.obj (padicSubfieldRingObj X ℓ F)))
      (((upperStar Ab.{u + 1} (U.f i)).mapMod _).obj P) := by
    intro i
    obtain ⟨ei⟩ := eP i
    apply free_of_iso _ ei.symm
    exact free_map (Mod.extendScalars _) (Mod.regularExtensionIso _)
      ⟨n i, ⟨Iso.refl _⟩⟩
  have hQ : IsLisseCoefficientModule (Profinite.continuousMapRingObj F) Q := by
    refine ⟨U, fun i ↦ ?_⟩
    let G := upperStar Ab.{u + 1} (U.f i)
    have hi := free_map (Mod.extendScalars (G.map r)) (Mod.regularExtensionIso _) (hP i)
    have hi' := free_of_iso hi
      ((pullbackExtendScalarsIso (U.f i) _ _ r).app P).symm
    exact free_map (Mod.extendScalars
      (condensedPullbackHom (Profinite.continuousMapRingObj F) (U.f i)))
      (Mod.regularExtensionIso _) hi'
  refine ⟨F, Q, hQ, ⟨?_⟩⟩
  have hsquare : r ≫ a = B.map a ≫ s :=
    (map_coefficientMap_comp_condensedPullbackHom
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) (𝟙 X)).symm
  exact (Mod.extendScalarsComp r a).symm.app P ≪≫
    (Mod.extendScalarsIsoOfEq hsquare).app P ≪≫
    (Mod.extendScalarsComp (B.map a) s).app P ≪≫
    (Mod.extendScalars s).mapIso eM ≪≫
    (CondensedRing.upperStarId (Profinite.padicAlgClRingObj ℓ) X).app L

end AlgebraicGeometry.ProEtale
