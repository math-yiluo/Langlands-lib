/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.Field.ULift
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import Mathlib.Algebra.Category.ModuleCat.Basic
import WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Ab
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Mathlib.Data.Matrix.Basic
import WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import Mathlib.LinearAlgebra.Matrix.ToLin
import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

/-! # Standard truncations on the ordinary bounded constructible derived category

Source: current blueprint prop-constructible-truncations. The categories here are full
subcategories of the ordinary derived categories of pulled-back condensed modules.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v uC vC uB vB
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry
namespace WeilConjectures

/-- The cohomology endofunctor specified by the proposition: truncate to degree i,
then shift by i. Its value is a degree-zero heart object.
Source: blueprint prop-constructible-truncations, cohomology display
(blueprint: prop-constructible-truncations). -/
def constructibleTruncationCohomology
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (t : TStructure C) (i : ℤ) : C ⥤ C :=
  (t.truncLE i ⋙ t.truncGE i) ⋙ shiftFunctor C i

end WeilConjectures

namespace AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

private theorem restricted_standard
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [ht : (DerivedCategory.TStructure.t.bounded ⊓
      DerivedCategory.homologyProperty P).IsTriangulated] :
    let Q := DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty P
    ∃ ht : Q.IsTriangulated,
      letI := ht
      ∃ t : TStructure Q.FullSubcategory,
        (∀ (K : Q.FullSubcategory) (n : ℤ),
          t.IsLE K n ↔ DerivedCategory.TStructure.t.IsLE K.obj n) ∧
        (∀ (K : Q.FullSubcategory) (n : ℤ),
          t.IsGE K n ↔ DerivedCategory.TStructure.t.IsGE K.obj n) ∧
        (∀ K, t.bounded K) ∧
        (∀ K, t.heart K ↔ ∀ i : ℤ, i ≠ 0 →
          IsZero ((DerivedCategory.homologyFunctor A i).obj K.obj)) ∧
        Nonempty (t.Heart P.FullSubcategory) ∧
        (∀ n : ℤ,
          Nonempty (t.truncLE n ⋙ Q.ι ≅ Q.ι ⋙ DerivedCategory.TStructure.t.truncLE n) ∧
          Nonempty (t.truncGE n ⋙ Q.ι ≅ Q.ι ⋙ DerivedCategory.TStructure.t.truncGE n)) := by
  let Q := DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty P
  have htr (K : DerivedCategory A) (hK : Q K) (n : ℤ) :
      Q ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
      Q ((DerivedCategory.TStructure.t.truncGE n).obj K) := by
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hK⟩ := hK
    exact ⟨⟨⟨⟨a, inferInstance⟩, ⟨n, inferInstance⟩⟩,
        DerivedCategory.homologyProperty_truncLE hK n⟩,
      ⟨⟨⟨n, inferInstance⟩, ⟨b, inferInstance⟩⟩,
        DerivedCategory.homologyProperty_truncGE hK n⟩⟩
  have : Q.HasInducedTStructure DerivedCategory.TStructure.t :=
    ObjectProperty.HasInducedTStructure.mk' htr
  let t := Q.tStructure DerivedCategory.TStructure.t
  refine ⟨ht, t, fun K n ↦ Q.tStructure_isLE_iff _ K n,
    fun K n ↦ Q.tStructure_isGE_iff _ K n, ?_, ?_, ?_, ?_⟩
  · intro K
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := K.property.1
    exact ⟨⟨a, (Q.tStructure_isGE_iff _ K a).mpr ha⟩,
      ⟨b, (Q.tStructure_isLE_iff _ K b).mpr hb⟩⟩
  · intro K
    rw [t.mem_heart_iff, Q.tStructure_isLE_iff, Q.tStructure_isGE_iff]
    change K.obj.IsLE 0 ∧ K.obj.IsGE 0 ↔ _
    rw [DerivedCategory.isLE_iff, DerivedCategory.isGE_iff]
    constructor
    · rintro ⟨hle, hge⟩ i hi
      rcases lt_or_gt_of_ne hi with hi | hi
      · exact hge i hi
      · exact hle i hi
    · intro h
      exact ⟨fun i hi ↦ h i (by omega), fun i hi ↦ h i (by omega)⟩
  · have hS (M : P.FullSubcategory) : Q ((DerivedCategory.singleFunctor A 0).obj M.obj) := by
      refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, ?_⟩
      intro i
      by_cases hi : i = 0
      · subst i
        exact P.prop_of_iso ((DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app
          M.obj).symm M.property
      · apply P.prop_of_isZero
        rcases lt_or_gt_of_ne hi with hi | hi
        · exact DerivedCategory.isZero_of_isGE _ 0 i hi
        · exact DerivedCategory.isZero_of_isLE _ 0 i hi
    let S := Q.lift (P.ι ⋙ DerivedCategory.singleFunctor A 0) hS
    refine ⟨{ ι := S, essImage_eq_heart := ?_ }⟩
    ext K
    constructor
    · rintro ⟨M, ⟨e⟩⟩
      apply t.heart.prop_of_iso e
      rw [t.mem_heart_iff, Q.tStructure_isLE_iff, Q.tStructure_isGE_iff]
      constructor
      · change DerivedCategory.TStructure.t.IsLE
          ((DerivedCategory.singleFunctor A 0).obj M.obj) 0
        infer_instance
      · change DerivedCategory.TStructure.t.IsGE
          ((DerivedCategory.singleFunctor A 0).obj M.obj) 0
        infer_instance
    · intro hK
      obtain ⟨hle, hge⟩ := (t.mem_heart_iff K).mp hK
      have : K.obj.IsLE 0 := (Q.tStructure_isLE_iff _ K 0).mp hle
      have : K.obj.IsGE 0 := (Q.tStructure_isGE_iff _ K 0).mp hge
      obtain ⟨M, ⟨e⟩⟩ := K.obj.exists_iso_singleFunctor_obj_of_isGE_of_isLE 0
      have hM : P M := P.prop_of_iso
        ((DerivedCategory.homologyFunctor A 0).mapIso e ≪≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app M) (K.property.2 0)
      exact ⟨⟨M, hM⟩, ⟨Q.isoMk e.symm⟩⟩
  · have : Q.ι.IsTExact t DerivedCategory.TStructure.t :=
      { isLE := fun K n h ↦ (Q.tStructure_isLE_iff _ K n).mp h
        isGE := fun K n h ↦ (Q.tStructure_isGE_iff _ K n).mp h }
    intro n
    exact ⟨⟨Q.ι.eTruncLTIso t _ (n + 1 : ℤ)⟩, ⟨Q.ι.eTruncGEIso t _ n⟩⟩

section Ordinary

variable {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  [MonObj R] [IsCommMonObj R]

/-- The standard bounded t-structure on the actual full constructible subcategory.
Its heart is the category of constructible module objects; the final comparisons identify
its truncations with the ambient canonical truncations, including their triangles.
Source: current blueprint prop-constructible-truncations, first paragraph
(blueprint: prop-constructible-truncations). -/
def OrdinaryConstructibleTruncations [(boundedConstructible R).IsTriangulated]
    (t : TStructure (BoundedConstructible R)) : Prop :=
  (∀ (K : BoundedConstructible R) (n : ℤ),
    t.IsLE K n ↔ DerivedCategory.TStructure.t.IsLE K.obj n) ∧
  (∀ (K : BoundedConstructible R) (n : ℤ),
    t.IsGE K n ↔ DerivedCategory.TStructure.t.IsGE K.obj n) ∧
  (∀ K, t.bounded K) ∧
  (∀ K, t.heart K ↔ ∀ i : ℤ, i ≠ 0 →
    IsZero ((DerivedCategory.homologyFunctor _ i).obj K.obj)) ∧
  Nonempty (t.Heart (ObjectProperty.FullSubcategory (IsConstructibleModuleObject R))) ∧
  (∀ n : ℤ,
    Nonempty (t.truncLE n ⋙ (boundedConstructible R).ι ≅
      (boundedConstructible R).ι ⋙ DerivedCategory.TStructure.t.truncLE n) ∧
    Nonempty (t.truncGE n ⋙ (boundedConstructible R).ι ≅
      (boundedConstructible R).ι ⋙ DerivedCategory.TStructure.t.truncGE n))

omit [IsCommMonObj R] in
private theorem constructible_zero_class :
    ObjectProperty.ContainsZero (IsConstructibleModuleObject R) := by
  obtain ⟨K, hK, hc⟩ := ObjectProperty.exists_prop_of_containsZero (boundedConstructible R)
  exact ⟨(DerivedCategory.homologyFunctor _ 0).obj K,
    (DerivedCategory.homologyFunctor _ 0).map_isZero hK, hc.2 0⟩

omit [IsCommMonObj R] in
private theorem ordinary_exists [(boundedConstructible R).IsTriangulated] :
    ∃ t : TStructure (BoundedConstructible R), OrdinaryConstructibleTruncations R t := by
  have : ObjectProperty.ContainsZero (IsConstructibleModuleObject R) := constructible_zero_class R
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsConstructibleModuleObject R) :=
    ⟨fun e h ↦ h.of_iso e⟩
  have : (DerivedCategory.TStructure.t.bounded ⊓
      DerivedCategory.homologyProperty (IsConstructibleModuleObject R)).IsTriangulated := by
    change (boundedConstructible R).IsTriangulated
    infer_instance
  obtain ⟨ht, t, h⟩ := restricted_standard (IsConstructibleModuleObject R)
  exact ⟨t, h⟩

end Ordinary

section Exchange

variable {X Y : Scheme.{u}}
  (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
  (S : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj S] [IsCommMonObj S]
  [(boundedConstructible R).IsTriangulated] [(boundedConstructible S).IsTriangulated]

end Exchange

end AlgebraicGeometry.ProEtale
