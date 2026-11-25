/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
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
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Closure of lisse and constructible coefficient sheaves

Source: Weil blueprint main-20261015, sec-six-functors-basics/sk-lem-coefficient-heart/
sk-lem-coefficient-heart-closure.md, clauses (1)--(2) and the concluding paragraph
(blueprint: lemma-constructible-sheaves).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private lemma heart_free_model
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Y : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : IsLisseCoefficientModule Λ M) : HasFiniteConstantLocalModel Λ Y M := by
  open MonoidalCategory MonObj Functor.LaxMonoidal Functor.OplaxMonoidal in
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨n, ⟨e⟩⟩ := hU i
  have : PreservesFiniteColimits (upperStarFromPoint (U.X i)) := by
    let : pointUpperStar.{u}.IsLeftAdjoint := pointUpperStarLowerStarAdjunction.isLeftAdjoint
    unfold upperStarFromPoint
    infer_instance
  let F := (upperStarFromPoint (U.X i)).mapMod Λ
  have : PreservesFiniteColimits F := inferInstance
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  have : PreservesFiniteBiproducts F := inferInstance
  let en : F.obj (Mod.finiteFree Λ n) ≅ Mod.finiteFree (condensedRingObj Λ (U.X i)) n :=
    F.mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫
      biproduct.mapIso (fun _ ↦ Mod.isoMk (Iso.refl _) (by simp [Mod.act]))
  exact ⟨Mod.finiteFree Λ n, ⟨n, n, 0, ⟨cokernelZeroIsoTarget.symm⟩⟩, ⟨e ≪≫ en.symm⟩⟩

private lemma heart_lisse_of_free
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (h : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj (condensedRingObj Λ X))
        (((upperStar Ab.{u + 1} (U.f i)).mapMod (condensedRingObj Λ X)).obj M)) :
    IsLisseCoefficientModule Λ M := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U, fun i ↦ ?_⟩
  let φ := condensedPullbackHom Λ (U.f i)
  exact free_of_iso (free_comap (inv φ) (hU i))
    ((Mod.extendScalarsIsoComapInv φ).app _).symm

private lemma heart_lfp_of_lisse
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (h : IsLisseCoefficientModule Λ M) :
    IsLocallyFinitelyPresented (condensedRingObj Λ X) M := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U, fun i ↦ ?_⟩
  let φ := condensedPullbackHom Λ (U.f i)
  exact fp_of_comap (inv φ)
    (fp_of_iso (fp_of_free (hU i)) ((Mod.extendScalarsIsoComapInv φ).app _))

private lemma heart_closure_classes {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C)
    (hi : ∀ {M N : C}, (M ≅ N) → P M → P N)
    (hk : ∀ {M N : C} (f : M ⟶ N), P M → P N → P (kernel f))
    (hc : ∀ {M N : C} (f : M ⟶ N), P M → P N → P (cokernel f))
    (he : ∀ Q : ShortComplex C, Q.ShortExact → P Q.X₁ → P Q.X₃ → P Q.X₂) :
    P.IsClosedUnderExtensions ∧ P.IsClosedUnderKernels ∧ P.IsClosedUnderCokernels := by
  refine ⟨⟨fun {Q} h h₁ h₃ ↦ he Q h h₁ h₃⟩, ⟨?_⟩, ⟨?_⟩⟩
  · rintro _ ⟨f, k, h, hMN⟩
    exact hi ((kernelIsKernel f).conePointUniqueUpToIso h) (hk f hMN.1 hMN.2)
  · rintro _ ⟨f, k, h, hMN⟩
    exact hi ((cokernelIsCokernel f).coconePointUniqueUpToIso h) (hc f hMN.1 hMN.2)

private lemma heart_abelian {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions] :
    Nonempty (Abelian P.FullSubcategory) ∧
      PreservesFiniteLimits P.ι ∧ PreservesFiniteColimits P.ι := by
  have : P.IsClosedUnderBinaryProducts := .mk' (by
    rintro _ ⟨D, hD⟩
    exact P.prop_of_iso ((biprod.isoProd _ _) ≪≫
      (HasLimit.isoOfNatIso (diagramIsoPair D)).symm)
      (P.prop_biprod (hD ⟨.left⟩) (hD ⟨.right⟩)))
  have : P.IsClosedUnderFiniteProducts := .mk'
  have : Abelian P.FullSubcategory := inferInstance
  have : HasBinaryBiproducts P.FullSubcategory :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have : ∀ {A B : P.FullSubcategory} (f : A ⟶ B),
      PreservesLimit (parallelPair f 0) P.ι := fun {_ _} f ↦ P.preservesKernels_ι f
  have : ∀ {A B : P.FullSubcategory} (f : A ⟶ B),
      PreservesColimit (parallelPair f 0) P.ι := fun {_ _} f ↦ P.preservesCokernels_ι f
  exact ⟨⟨inferInstance⟩, Functor.preservesFiniteLimits_of_preservesKernels P.ι,
    Functor.preservesFiniteColimits_of_preservesCokernels P.ι⟩

private lemma heart_constructible_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (e : M ≅ N) (hM : IsConstructibleModuleObject R M) :
    IsConstructibleModuleObject R N := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  obtain ⟨U, hU⟩ := hS a
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨n, m, f, ⟨e'⟩⟩ := hU i
  exact ⟨n, m, f, ⟨(((upperStar Ab.{u + 1} (S.immersion a)).mapMod R ⋙
    (upperStar Ab.{u + 1} (U.f i)).mapMod _).mapIso e).symm ≪≫ e'⟩⟩

private lemma heart_constructible_zero {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hM : IsZero M) : IsConstructibleModuleObject R M := by
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  refine ⟨S, fun a ↦ ?_⟩
  let U : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a) :=
    .singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _)
  refine ⟨U, fun i ↦ ?_⟩
  refine ⟨0, 0, 𝟙 _, ⟨?_⟩⟩
  let F := (upperStar Ab.{u + 1} (S.immersion a)).mapMod R
  let G := (upperStar Ab.{u + 1} (U.f i)).mapMod
    ((upperStar Ab.{u + 1} (S.immersion a)).obj R)
  exact (G.map_isZero (F.map_isZero hM)).iso (isZero_cokernel_of_epi (𝟙 _))

private lemma heart_strata {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    (Q : ∀ Y : Scheme.{u}, (Y ⟶ X) → Prop) :
    (∃ S : Scheme.Stratification X, ∀ a : Fin S.n, Q (S.domain a) (S.immersion a)) ↔
      ∃ R : X.FiniteLocallyClosedStratification, ∀ a : Fin R.n,
        Q (R.domain a) (R.immersion a) := by
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨{ n := S.n
             stratum := S.stratum
             isLocallyClosed_stratum := S.isLocallyClosed_stratum
             iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
             pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
             domain := S.domain
             immersion := S.immersion
             isImmersion := S.isImmersion
             range_immersion := S.range_immersion }, hS⟩
  · rintro ⟨R, hR⟩
    exact ⟨Scheme.Stratification.ofNoetherianSpace R.n R.stratum
      R.isLocallyClosed_stratum R.iUnion_stratum_eq_univ R.pairwise_disjoint_stratum
      R.domain R.immersion R.isImmersion R.range_immersion, hR⟩

private lemma heart_stratified_lisse
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    (hlocal : ∀ (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj A Y)),
      IsLisseCoefficientModule A M ↔ IsLocallyFinitelyPresented (condensedRingObj A Y) M)
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A X)) :
    IsConstantModelConstructible A X M ↔
      ∃ R : X.FiniteLocallyClosedStratification, ∀ a : Fin R.n,
        IsLisseCoefficientModule A ((CondensedRing.upperStar A (R.immersion a)).obj M) := by
  rw [← heart_strata (fun Y f ↦
    IsLisseCoefficientModule A ((CondensedRing.upperStar A f).obj M))]
  constructor
  · intro hM
    have hfinite : IsFiniteConstantStratified A X M := by
      simpa only [IsConstantModelConstructible,
        ite_eq_left (show CompactSpace X ∧ QuasiSeparatedSpace X from
          ⟨inferInstance, inferInstance⟩)] using hM
    obtain ⟨S, hS⟩ := hfinite
    refine ⟨S, fun a ↦ ?_⟩
    have : TopologicalSpace.NoetherianSpace (S.domain a) :=
      (S.immersion a).isEmbedding.isInducing.noetherianSpace
    exact (hlocal _ _).mpr ((hS a).isLocallyFinitelyPresented _)
  · rintro ⟨S, hS⟩
    rw [IsConstantModelConstructible, ite_eq_left ⟨inferInstance, inferInstance⟩]
    exact ⟨S, fun a ↦ heart_free_model A _ (hS a)⟩

private lemma heart_closure_generic
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj A] [IsCommMonObj A]
    (hLF : ∀ (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj A Y))
      (_hM : IsLocallyFinitelyPresented (condensedRingObj A Y) M),
      ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i,
        Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj (condensedRingObj A Y))
          (((upperStar Ab.{u + 1} (U.f i)).mapMod (condensedRingObj A Y)).obj M)) :
    (∀ (S : Scheme.{u}) [TopologicalSpace.NoetherianSpace S],
      ObjectProperty.IsClosedUnderExtensions
        (IsLisseCoefficientModule A (X := S)) ∧
      ObjectProperty.IsClosedUnderKernels
        (IsLisseCoefficientModule A (X := S)) ∧
      ObjectProperty.IsClosedUnderCokernels
        (IsLisseCoefficientModule A (X := S))) ∧
    (∀ (X : Scheme.{u}) [IsNoetherian X],
      ObjectProperty.IsClosedUnderKernels
        (IsConstantModelConstructible A X) ∧
      ObjectProperty.IsClosedUnderCokernels
        (IsConstantModelConstructible A X) ∧
      ObjectProperty.IsClosedUnderExtensions
        (IsConstantModelConstructible A X) ∧
      Nonempty (Abelian (ConstantModelConstructible A X)) ∧
      PreservesFiniteLimits
        (ObjectProperty.ι (IsConstantModelConstructible
          A X)) ∧
      PreservesFiniteColimits
        (ObjectProperty.ι (IsConstantModelConstructible
          A X)) ∧
      ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj A X),
        IsConstantModelConstructible A X M ↔
          ∃ R : X.FiniteLocallyClosedStratification, ∀ a : Fin R.n,
            IsLisseCoefficientModule A
              ((CondensedRing.upperStar A (R.immersion a)).obj M)) := by
  classical
  have hlisse (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj A Y)) :
      IsLisseCoefficientModule A M ↔ IsLocallyFinitelyPresented (condensedRingObj A Y) M :=
    ⟨heart_lfp_of_lisse A, fun h ↦ heart_lisse_of_free A (hLF Y M h)⟩
  constructor
  · intro S hS
    have h := lfp_serre_of_locally_free freeEpiLocalSplitting (condensedRingObj A S) (hLF S)
    apply heart_closure_classes (IsLisseCoefficientModule A (X := S))
    · intro M N e hM
      exact (hlisse S N).mpr (lfp_of_iso ((hlisse S M).mp hM) e)
    · intro M N f hM hN
      exact (hlisse S _).mpr (h.1 M N f ((hlisse S M).mp hM)
        ((hlisse S N).mp hN)).1
    · intro M N f hM hN
      exact (hlisse S _).mpr (h.1 M N f ((hlisse S M).mp hM)
        ((hlisse S N).mp hN)).2
    · intro Q hQ h₁ h₃
      exact (hlisse S _).mpr (h.2 Q hQ ((hlisse S _).mp h₁) ((hlisse S _).mp h₃))
  · intro X hX
    have hmod (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj A X)) :
        IsConstantModelConstructible A X M ↔
          IsConstructibleModuleObject (condensedRingObj A X) M := by
      rw [IsConstantModelConstructible, ite_eq_left ⟨inferInstance, inferInstance⟩]
      constructor
      · rintro ⟨S, hS⟩
        refine ⟨S, fun a ↦ ?_⟩
        let φ := condensedPullbackHom A (S.immersion a)
        have h := (hS a).isLocallyFinitelyPresented _
        exact lfp_of_comap (inv φ)
          (lfp_of_iso h ((Mod.extendScalarsIsoComapInv φ).app _))
      · rintro ⟨S, hS⟩
        refine ⟨S, fun a ↦ ?_⟩
        have : TopologicalSpace.NoetherianSpace (S.domain a) :=
          (S.immersion a).isEmbedding.isInducing.noetherianSpace
        let φ := condensedPullbackHom A (S.immersion a)
        have h := lfp_of_iso (lfp_comap (inv φ) (hS a))
          ((Mod.extendScalarsIsoComapInv φ).app _).symm
        exact heart_free_model A _ ((hlisse _ _).mpr h)
    let P : ObjectProperty _ := IsConstantModelConstructible A X
    have hi : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦
      (hmod _).mpr (heart_constructible_iso e ((hmod _).mp h))⟩
    have h := condensed_constructible_serre_of_locally_free freeEpiLocalSplitting A hLF X
    obtain ⟨he, hk, hc⟩ := heart_closure_classes P
      (fun e h ↦ P.prop_of_iso e h)
      (fun f hM hN ↦ (hmod _).mpr (h.1 _ _ f ((hmod _).mp hM) ((hmod _).mp hN)).1)
      (fun f hM hN ↦ (hmod _).mpr (h.1 _ _ f ((hmod _).mp hM) ((hmod _).mp hN)).2)
      (fun Q hQ h₁ h₃ ↦ (hmod _).mpr (h.2 Q hQ ((hmod _).mp h₁) ((hmod _).mp h₃)))
    have : P.IsClosedUnderExtensions := he
    have : P.IsClosedUnderKernels := hk
    have : P.IsClosedUnderCokernels := hc
    have : P.ContainsZero := by
      obtain ⟨Z, hZ⟩ := (inferInstance : HasZeroObject
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A X))).zero
      exact ⟨⟨Z, hZ, (hmod _).mpr (heart_constructible_zero Z hZ)⟩⟩
    obtain ⟨hab, hlim, hcolim⟩ := heart_abelian P
    refine ⟨hk, hc, he, hab, hlim, hcolim, ?_⟩
    exact heart_stratified_lisse A hlisse X

/-- Lisse coefficient sheaves are closed under extensions, kernels and cokernels on a
 topologically Noetherian scheme. On a Noetherian scheme, constructible sheaves form an
 abelian full subcategory with exact inclusion and are exactly the sheaves lisse on a
 finite stratification.
Source: blueprint coefficient-heart-closure, clauses (1)--(2) and concluding paragraph
(blueprint: lemma-constructible-sheaves).

Proof: identify lisse modules with locally finitely presented modules using the existing
finite-field and bounded-image algebraic-closure local-triviality results. The proved
conditional Serre helpers in `CondensedConstructibleSerre` then give local kernel,
cokernel and extension closure: cokernels have finite presentations, and local basis
lifts split epimorphisms onto free modules and extensions. On a Noetherian scheme,
finite constant stratified models are equivalent to stratified local finite presentation.
The same generic helpers refine the two stratifications and use exact restriction on
each stratum, giving global closure. Zero has an identity presentation on the identity
stratification. Mathlib's full-subcategory construction gives abelianity, and preservation
of kernels and cokernels gives exactness of the inclusion. Finally the Noetherian-space
criterion that locally closed sets are constructible identifies the two finite
stratification conventions. Rank zero, empty strata and the empty scheme are included. -/
theorem coefficientHeart_closure (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ) :
    (∀ (S : Scheme.{u}) [TopologicalSpace.NoetherianSpace S],
      ObjectProperty.IsClosedUnderExtensions
        (IsLisseCoefficientModule (coefficientHeartRingObj Λ) (X := S)) ∧
      ObjectProperty.IsClosedUnderKernels
        (IsLisseCoefficientModule (coefficientHeartRingObj Λ) (X := S)) ∧
      ObjectProperty.IsClosedUnderCokernels
        (IsLisseCoefficientModule (coefficientHeartRingObj Λ) (X := S))) ∧
    (∀ (X : Scheme.{u}) [IsNoetherian X],
      ObjectProperty.IsClosedUnderKernels
        (IsConstantModelConstructible (coefficientHeartRingObj Λ) X) ∧
      ObjectProperty.IsClosedUnderCokernels
        (IsConstantModelConstructible (coefficientHeartRingObj Λ) X) ∧
      ObjectProperty.IsClosedUnderExtensions
        (IsConstantModelConstructible (coefficientHeartRingObj Λ) X) ∧
      Nonempty (Abelian (ConstantModelConstructible (coefficientHeartRingObj Λ) X)) ∧
      PreservesFiniteLimits
        (ObjectProperty.ι (IsConstantModelConstructible
          (coefficientHeartRingObj Λ) X)) ∧
      PreservesFiniteColimits
        (ObjectProperty.ι (IsConstantModelConstructible
          (coefficientHeartRingObj Λ) X)) ∧
      ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (coefficientHeartRingObj Λ) X),
        IsConstantModelConstructible (coefficientHeartRingObj Λ) X M ↔
          ∃ R : X.FiniteLocallyClosedStratification, ∀ a : Fin R.n,
            IsLisseCoefficientModule (coefficientHeartRingObj Λ)
              ((CondensedRing.upperStar (coefficientHeartRingObj Λ) (R.immersion a)).obj M)) := by
  apply heart_closure_generic
  intro Y _ M hM
  rcases hΛ with ⟨E, hE, rfl⟩ | rfl
  · exact finite_lf ℓ ⟨E, hE⟩ Y M hM
  · exact algcl_lf ℓ Y M hM

end AlgebraicGeometry.ProEtale
