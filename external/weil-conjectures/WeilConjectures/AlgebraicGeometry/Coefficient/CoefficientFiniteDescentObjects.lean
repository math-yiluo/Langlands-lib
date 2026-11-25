/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import Mathlib.AlgebraicGeometry.Noetherian
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
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Finite coefficient descent of bounded constructible objects

Source: blueprint main-20261015, chap-Construction-of-f,
sk-thm-sfb-qlbar-two-colimit/sk-lem-coefficient-finite-descent-objects.md and its proof
(blueprint: lemma-descent-finite-coefficient-field--2).

The constructibility convention is the finite constant local model convention of
`det-def-sfb-constructible-tor-amplitude`. The scalar extensions are the specified left
derived functors on the unbounded categories of internal modules over pulled-back
condensed rings. Isomorphisms are in these ambient derived categories.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open MonoidalCategory MonObj Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma free_hasConstantModel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Y : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i,
      Mod.IsFree (condensedRingObj Λ (U.X i))
        ((CondensedRing.upperStar Λ (U.f i)).obj M)) :
    HasFiniteConstantLocalModel Λ Y M := by
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
  refine ⟨Mod.finiteFree Λ n, ⟨n, n, 0, ⟨cokernelZeroIsoTarget.symm⟩⟩, ⟨e ≪≫ en.symm⟩⟩

open MonoidalCategory MonObj in
private lemma constantModel_eq_of_localFree
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hLF : ∀ (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      IsLocallyFinitelyPresented (condensedRingObj Λ Y) M →
      ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i,
        Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj (condensedRingObj Λ Y))
          (((upperStar Ab.{u + 1} (U.f i)).mapMod (condensedRingObj Λ Y)).obj M))
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [TopologicalSpace.NoetherianSpace X] :
    constantModelBoundedConstructible Λ X = boundedConstructible (condensedRingObj Λ X) := by
  have hmod (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :
      IsConstantModelConstructible Λ X M ↔
        IsConstructibleModuleObject (condensedRingObj Λ X) M := by
    rw [show IsConstantModelConstructible Λ X M = IsFiniteConstantStratified Λ X M from
      ite_eq_left ⟨inferInstance, inferInstance⟩]
    constructor
    · rintro ⟨S, hS⟩
      refine ⟨S, fun a ↦ ?_⟩
      let φ := condensedPullbackHom Λ (S.immersion a)
      have h := (hS a).isLocallyFinitelyPresented _
      exact lfp_of_comap (inv φ)
        (lfp_of_iso h ((Mod.extendScalarsIsoComapInv φ).app _))
    · rintro ⟨S, hS⟩
      refine ⟨S, fun a ↦ ?_⟩
      have : TopologicalSpace.NoetherianSpace (S.domain a) :=
        (S.immersion a).isEmbedding.isInducing.noetherianSpace
      let φ := condensedPullbackHom Λ (S.immersion a)
      have h := lfp_of_iso (lfp_comap (inv φ) (hS a))
        ((Mod.extendScalarsIsoComapInv φ).app _).symm
      obtain ⟨U, hU⟩ := hLF _ _ h
      apply free_hasConstantModel Λ _
      refine ⟨U, fun i ↦ ?_⟩
      let ψ := condensedPullbackHom Λ (U.f i)
      exact free_of_iso (free_comap (inv ψ) (hU i))
        ((Mod.extendScalarsIsoComapInv ψ).app _).symm
  funext K
  apply propext
  exact and_congr_right fun _ ↦ forall_congr' fun n ↦ hmod _

/-- Finite descent of bounded constructible algebraic-closure complexes over a Noetherian
scheme. The base field of `coefficient_finite_descent_objects` only makes X Noetherian.
Source: blueprint lemma-descent-finite-coefficient-field--2
(blueprint: lemma-descent-finite-coefficient-field--2). -/
theorem coefficient_finite_descent_objects_of_isNoetherian
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsNoetherian X] :
    (∀ K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X,
      ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
        (K_E : ConstantModelBoundedConstructible (Profinite.continuousMapRingObj E) X),
        Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K_E.obj ≅ K.obj)) ∧
    (∀ (K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X)
      (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (K_E : ConstantModelBoundedConstructible (Profinite.continuousMapRingObj E) X),
      Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K_E.obj ≅ K.obj) →
      ∀ (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (h : E ≤ F),
        constantModelBoundedConstructible (Profinite.continuousMapRingObj F) X
          ((derivedExtendScalarsSubfield X ℓ h).obj K_E.obj) ∧
        Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ F).obj
          ((derivedExtendScalarsSubfield X ℓ h).obj K_E.obj) ≅ K.obj)) := by
  have hE (E : PadicAlgCl.FiniteIntermediateField ℓ) :
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X =
        boundedConstructible (padicSubfieldRingObj X ℓ E) :=
    constantModel_eq_of_localFree _ (finite_lf ℓ E) X
  have hΩ : constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X =
      boundedConstructible (padicAlgClRingObj X ℓ) :=
    constantModel_eq_of_localFree _ (algcl_lf ℓ) X
  constructor
  · intro K
    let K' : PadicAlgClConstructible X ℓ := ⟨K.obj, (congrFun hΩ K.obj).mp K.property⟩
    obtain ⟨E, L, ⟨e⟩⟩ := constructibleCocone_essSurjObj X ℓ K'
    exact ⟨E, ⟨L.obj, (congrFun (hE E) L.obj).mpr L.property⟩,
      ⟨(boundedConstructible (padicAlgClRingObj X ℓ)).ι.mapIso e⟩⟩
  · intro K E K_E hK F h
    constructor
    · exact (congrFun (hE F) _).mpr
        (boundedConstructible_derivedExtendScalarsSubfield_obj X ℓ h
          ⟨K_E.obj, (congrFun (hE E) K_E.obj).mp K_E.property⟩)
    · obtain ⟨e⟩ := hK
      exact ⟨(derivedExtendScalarsCompIso X ℓ h).app K_E.obj ≪≫ e⟩

/-- Every bounded constructible algebraic-closure coefficient complex has a finite-field
model, and every such model remains a model after any finite enlargement of the field.
Source: blueprint main-20261015, lemma-descent-finite-coefficient-field,
sk-lem-coefficient-finite-descent-objects.md, both assertions
(blueprint: lemma-descent-finite-coefficient-field--2).

Proof plan, following the node's five steps:
1. A standing scheme is Noetherian: Spec k is Noetherian and finite type preserves this
(lemma-descent-finite-coefficient-field--2). Its locally closed strata are Noetherian and
qcqs, so the hypotheses of lisse descent and finite constructible generation hold.
2. Models persist by lemma-extension-scalars-preserves-dctf--1 and the transitivity comparison
of definition-sp-scalar-extension--2. Scalar extensions are exact by prose-03-27,
prose-03-27 and the right exact tensor adjunction lemma-descent-finite-coefficient-field--2.
The exact-functor identification of lemma-descent-finite-coefficient-field--2 and
situation-conventions makes these specified derived functors
termwise, triangulated and compatible with shifts. Thus shifts of models are models by
corollary-coefficient-heart-b--1. Finite composita put any two models over a common
field (lemma-descent-finite-coefficient-field--2). This proves the second assertion.
3. For a triangle A → K → B → A[1], put models of A and B over a common E. Transport the
connecting map to their extensions. By lemma-descent-finite-coefficient-field--1 (3), with
r = 1, it is represented over some finite F containing E. Complete that representative to
a triangle B_F → A_F[1] → C_F → B_F[1] using TR1 of lemma-descent-finite-coefficient-field--2.
Two inverse rotations give A_F → C_F[-1] → B_F → A_F[1], with the original connecting map
and no sign change. Set K_F = C_F[-1]; triangulated closure puts it in Dbc(X,F). After
scalar extension, rotate to compare connecting maps. TR3 and
lemma-descent-finite-coefficient-field--2 give an isomorphism to the given triangle. Hence K
descends. Rotation also gives descent of cones between descended objects.
4. For a generator a_!L[n] of corollary-coefficient-heart-b--2, its locally closed
stratum is qcqs by step 1. Apply lemma-descent-lisse-qbar-sheaves-finite--1 (1) there to get
L_E. The converse generation assertion puts a_!L_E[n] in Dbc(X,E).
The identification in prose-03-27 is the same condensed inclusion on
both schemes. Thus proposition-six-operations-change-coefficients (2), including the closed
immersion factor, and shift compatibility identify its extension with a_!L[n].
5. Apply the finite generating sequence of corollary-coefficient-heart-b--2 to K.
Induct through it using step 4 for generators, step 3 for cones, step 2 for common fields
and shifts, and composition for isomorphisms. Zero has its zero model over the base field,
also a rank-zero generator. Finitely many choices and composita yield one finite field E;
no infinite enlargement occurs. -/
theorem coefficient_finite_descent_objects
    (k : Type u) [Field k] (p ℓ : ℕ) [CharP k p] [Fact ℓ.Prime]
    (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    (∀ K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X,
      ∃ (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
        (K_E : ConstantModelBoundedConstructible (Profinite.continuousMapRingObj E) X),
        Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K_E.obj ≅ K.obj)) ∧
    (∀ (K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X)
      (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
      (K_E : ConstantModelBoundedConstructible (Profinite.continuousMapRingObj E) X),
      Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K_E.obj ≅ K.obj) →
      ∀ (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (h : E ≤ F),
        constantModelBoundedConstructible (Profinite.continuousMapRingObj F) X
          ((derivedExtendScalarsSubfield X ℓ h).obj K_E.obj) ∧
        Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ F).obj
          ((derivedExtendScalarsSubfield X ℓ h).obj K_E.obj) ≅ K.obj)) := by
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsNoetherian X := {}
  exact coefficient_finite_descent_objects_of_isNoetherian ℓ X

end AlgebraicGeometry.ProEtale
