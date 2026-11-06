import Langlands.AlgebraicGeometry.PointTopology.ProductTensorWeilTopology
import Langlands.AlgebraicGeometry.PointTopology.NumberFieldSIntegerModelCompatibility

noncomputable section

universe u

open CategoryTheory Topology IsDedekindDomain
open _root_.AlgebraicGeometry
open scoped NumberField TensorProduct NumberField.LiesOver
  Langlands.Global Langlands.Global.NumberFieldSIntegers
  Langlands.Global.NumberFieldSIntegerLocalTensor
  Langlands.Global.AdelicFunctoriality.FiniteExtension
  Langlands.Global.AdelicFunctoriality.InfiniteExtension
  Langlands.Global.AdelicFunctoriality.IntegralTensor
  Langlands.Global.AdelicFunctoriality.IntegralTopology

namespace Langlands.Global.NumberFieldSIntegerLevelWeil

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open AdelicFunctoriality

set_option backward.isDefEq.respectTransparency false

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (S : Finset (FinitePlace K))

/-- All original upper places above an original lower level coordinate, including infinite places. -/
def Above : NumberFieldLevelFactorIndex K S → Type u
  | .inl p => InfinitePlacesAbove L p
  | .inr (.inl p) => FinitePlacesAbove L p.1
  | .inr (.inr p) => FinitePlacesAbove L p.1

scoped instance aboveFinite (i) : Finite (Above K L S i) := by
  cases i with
  | inl p => exact inferInstanceAs (Finite (InfinitePlacesAbove L p))
  | inr z => cases z <;> dsimp [Above] <;> infer_instance

/-- The original upper completed field or completed integer ring at this coordinate. -/
def upperFactor (i : NumberFieldLevelFactorIndex K S) : Above K L S i → Type u :=
  match i with
  | .inl _ => fun q => q.1.Completion
  | .inr (.inl _) => fun q => q.1.adicCompletion L
  | .inr (.inr _) => fun q => q.1.adicCompletionIntegers L

scoped instance upperCommRing (i) (q : Above K L S i) :
    CommRing (upperFactor K L S i q) := by
  cases i with
  | inl p => dsimp [upperFactor]; infer_instance
  | inr z => cases z <;> dsimp [upperFactor] <;> infer_instance

scoped instance upperTopology (i) (q : Above K L S i) :
    TopologicalSpace (upperFactor K L S i q) := by
  cases i with
  | inl p => dsimp [upperFactor]; infer_instance
  | inr z => cases z <;> dsimp [upperFactor] <;> infer_instance

scoped instance upperTopologicalRing (i) (q : Above K L S i) :
    IsTopologicalRing (upperFactor K L S i q) := by
  cases i with
  | inl p => dsimp [upperFactor]; infer_instance
  | inr z => cases z <;> dsimp [upperFactor] <;> infer_instance

scoped instance upperLocalRing (i) (q : Above K L S i) :
    IsLocalRing (upperFactor K L S i q) := by
  cases i with
  | inl p => dsimp [upperFactor]; infer_instance
  | inr z => cases z <;> dsimp [upperFactor] <;> infer_instance

scoped instance upperOpenUnits (i) (q : Above K L S i) :
    IsOpenUnits (upperFactor K L S i q) := by
  cases i with
  | inl p => dsimp [upperFactor]; infer_instance
  | inr z => cases z <;> dsimp [upperFactor] <;> infer_instance

scoped instance lowerOpenUnits (i : NumberFieldLevelFactorIndex K S) :
    IsOpenUnits (NumberFieldLevelFactor K S i) := by
  cases i with
  | inl p => dsimp [NumberFieldLevelFactor]; infer_instance
  | inr z => cases z <;> dsimp [NumberFieldLevelFactor] <;> infer_instance

scoped instance upperCoefficientAlgebra (i) (q : Above K L S i) :
    Algebra (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) (upperFactor K L S i q) := by
  cases i with
  | inl p => exact inferInstanceAs (Algebra
      (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
        Set (FinitePlace L)).integer L) q.1.Completion)
  | inr z =>
    cases z with
    | inl p => exact inferInstanceAs (Algebra
        (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
          Set (FinitePlace L)).integer L) (q.1.adicCompletion L))
    | inr p =>
      letI : Fact (p.1 ∉ S) := ⟨p.2⟩
      exact NumberFieldSIntegerLocalTensor.upperCompletedAlgebra K S p.1 L q

scoped instance lowerFactorAlgebra (i) (q : Above K L S i) :
    Algebra (NumberFieldLevelFactor K S i) (upperFactor K L S i q) := by
  cases i with
  | inl p => dsimp [NumberFieldLevelFactor, upperFactor]; infer_instance
  | inr z => cases z <;> dsimp [NumberFieldLevelFactor, upperFactor] <;> infer_instance

scoped instance localFinite (i) (q : Above K L S i) :
    Module.Finite (NumberFieldLevelFactor K S i) (upperFactor K L S i q) := by
  cases i with
  | inl p => exact InfiniteExtension.local_finite p q.1
  | inr z =>
    cases z with
    | inl p => exact FiniteExtension.local_finite p.1 q.1
    | inr p => exact IntegralTopology.localFinite p.1 q

scoped instance localProjective (i) (q : Above K L S i) :
    Module.Projective (NumberFieldLevelFactor K S i) (upperFactor K L S i q) := by
  cases i with
  | inl p =>
    change Module.Projective p.Completion q.1.Completion
    let : Module.Free p.Completion q.1.Completion := Module.Free.of_divisionRing _ _
    exact Module.Projective.of_free
  | inr z =>
    cases z with
    | inl p =>
      change Module.Projective (p.1.adicCompletion K) (q.1.adicCompletion L)
      let : Module.Free (p.1.adicCompletion K) (q.1.adicCompletion L) :=
        Module.Free.of_divisionRing _ _
      exact Module.Projective.of_free
    | inr p => exact IntegralTopology.localProjective p.1 q

scoped instance localModuleTopology (i) (q : Above K L S i) :
    IsModuleTopology (NumberFieldLevelFactor K S i) (upperFactor K L S i q) := by
  cases i with
  | inl p =>
    let := infiniteCompletionNontriviallyNormedField p
    change IsModuleTopology p.Completion q.1.Completion
    exact isModuleTopologyOfFiniteDimensional
  | inr z =>
    cases z with
    | inl p =>
      let : NontriviallyNormedField (p.1.adicCompletion K) :=
        Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
      change IsModuleTopology (p.1.adicCompletion K) (q.1.adicCompletion L)
      exact isModuleTopologyOfFiniteDimensional
    | inr p => exact IntegralTopology.moduleTopology p.1 q

private def tensorData (i : NumberFieldLevelFactorIndex K S) :
    { e : NumberFieldLevelFactor K S i ⊗[(S : Set (FinitePlace K)).integer K]
        (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
          Set (FinitePlace L)).integer L) ≃ₐ[NumberFieldLevelFactor K S i]
        (∀ q : Above K L S i, upperFactor K L S i q) //
      ∀ (b : (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
          Set (FinitePlace L)).integer L)) (q : Above K L S i),
        e (1 ⊗ₜ[(S : Set (FinitePlace K)).integer K] b) q =
          algebraMap (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
            Set (FinitePlace L)).integer L) (upperFactor K L S i q) b } := by
  cases i with
  | inl p =>
    have h : instAdelicLevelModelPoints10 K S (.inl p) =
        Subalgebra.toAlgebra (α := p.Completion) ((S : Set (FinitePlace K)).integer K) :=
      Algebra.algebra_ext _ _ fun _ => rfl
    rw [h]
    exact ⟨NumberFieldSIntegerInfiniteTensor.tensorEquiv K L S p,
      NumberFieldSIntegerInfiniteTensor.tensorEquiv_one_tmul K L S p⟩
  | inr z =>
    cases z with
    | inl p =>
      have h : instAdelicLevelModelPoints10 K S (.inr (.inl p)) =
          Subalgebra.toAlgebra (α := p.1.adicCompletion K) ((S : Set (FinitePlace K)).integer K) :=
        Algebra.algebra_ext _ _ fun _ => rfl
      rw [h]
      exact ⟨NumberFieldSIntegerFieldTensor.tensorEquiv K L S p.1,
        NumberFieldSIntegerFieldTensor.tensorEquiv_one_tmul K L S p.1⟩
    | inr p =>
      letI : Fact (p.1 ∉ S) := ⟨p.2⟩
      exact ⟨NumberFieldSIntegerLocalTensor.completedTensorEquiv K S p.1 L,
        NumberFieldSIntegerLocalTensor.completedTensorEquiv_one_tmul K S p.1 L⟩

/-- Every original infinite, finite-field and finite-integer coordinate has its proved tensor comparison. -/
def tensorEquiv (i : NumberFieldLevelFactorIndex K S) :
    NumberFieldLevelFactor K S i ⊗[(S : Set (FinitePlace K)).integer K]
      (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
        Set (FinitePlace L)).integer L) ≃ₐ[NumberFieldLevelFactor K S i]
      (∀ q : Above K L S i, upperFactor K L S i q) :=
  (tensorData K L S i).1

@[simp]
theorem tensorEquiv_one_tmul (i : NumberFieldLevelFactorIndex K S)
    (b : (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L)) (q : Above K L S i) :
    tensorEquiv K L S i (1 ⊗ₜ[(S : Set (FinitePlace K)).integer K] b) q =
      algebraMap (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
        Set (FinitePlace L)).integer L) (upperFactor K L S i q) b :=
  (tensorData K L S i).2 b q

variable
  (Y : Over (Spec (CommRingCat.of
    ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)))))
  [LocallyOfFiniteType Y.hom] [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
  (n : ℕ)
  (j : Y.left ⟶ ProjectiveSpace
    ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) n) [IsImmersion j]
  (hj : j ≫ projectiveSpaceToSpec
    ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) n = Y.hom)

/-- Actual lower adelic-level Weil points have the product topology of every original upper local factor. -/
def levelPointHomeomorph :
    letI : TopologicalSpace
        (RingPoint (((S : Set (FinitePlace K)).integer K))
          (affineChartWeilRestriction
            (((S : Set (FinitePlace K)).integer K)) _ Y)
          (numberFieldAdeleLevel K (S))) :=
      numberFieldLevelModelPointTopology K (S)
        (affineChartWeilRestriction
          (((S : Set (FinitePlace K)).integer K)) _ Y)
    letI : ∀ z : Σ i, Above K L S i, TopologicalSpace
        (RingPoint
          ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) Y
          (upperFactor K L S z.1 z.2)) :=
      fun z => schemePointTopology
        ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) Y
        (upperFactor K L S z.1 z.2)
    RingPoint (((S : Set (FinitePlace K)).integer K))
        (affineChartWeilRestriction
          (((S : Set (FinitePlace K)).integer K)) _ Y)
        (numberFieldAdeleLevel K (S)) ≃ₜ
      (∀ z : Σ i, Above K L S i,
        RingPoint
          ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) Y
          (upperFactor K L S z.1 z.2)) := by
  let R₀ := ((S : Set (FinitePlace K)).integer K)
  let B₀ := (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)
  let S₀ := S
  let C₀ := NumberFieldLevelFactor K S₀
  let W := affineChartWeilRestriction R₀ B₀ Y
  letI := isSeparated_of_projectiveImmersion B₀ Y n j hj
  letI : TopologicalSpace (RingPoint R₀ W (numberFieldAdeleLevel K S₀)) :=
    numberFieldLevelModelPointTopology K S₀ W
  letI : TopologicalSpace (RingPoint R₀ W (∀ i, C₀ i)) :=
    localProductPointTopology R₀ C₀ W
  letI : ∀ z : Σ i, Above K L S i,
      TopologicalSpace (RingPoint B₀ Y (upperFactor K L S z.1 z.2)) :=
    fun z => schemePointTopology B₀ Y (upperFactor K L S z.1 z.2)
  let E := ringPointChangeRingEquiv R₀ W (numberFieldLevelFactorAlgEquiv K S₀)
  have hind : IsInducing (E : _ → _) :=
    ⟨numberFieldLevelModelPointTopology_eq K S₀ W⟩
  let H := IsHomeomorph.homeomorph E
    (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨⟨hind, E.injective⟩, E.surjective⟩)
  exact H.trans (productTensorWeilPointHomeomorph R₀ B₀ C₀
    (Above K L S) (upperFactor K L S) (tensorEquiv K L S)
    (tensorEquiv_one_tmul K L S) Y
    (hasFiniteAffineNeighborhoods_of_projectiveImmersion B₀ n j))

/-- Each level component is the original local Weil map after the literal original level projection. -/
theorem levelPointHomeomorph_component
    (p : RingPoint (((S : Set (FinitePlace K)).integer K))
      (affineChartWeilRestriction
        (((S : Set (FinitePlace K)).integer K)) _ Y)
      (numberFieldAdeleLevel K (S)))
    (i : NumberFieldLevelFactorIndex K (S))
    (q : Above K L S i) :
    levelPointHomeomorph K L S Y n j hj p ⟨i, q⟩ =
      completedTensorWeilRestrictionPointMap
        (((S : Set (FinitePlace K)).integer K)) _
        (NumberFieldLevelFactor K (S) i)
        (upperFactor K L S i) (tensorEquiv K L S i)
        (tensorEquiv_one_tmul K L S i) Y
        (p.changeRing (numberFieldLevelFactorAlgHom K
          (S) i)) q := by
  let R₀ := ((S : Set (FinitePlace K)).integer K)
  let B₀ := (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)
  let S₀ := S
  let C₀ := NumberFieldLevelFactor K S₀
  let W := affineChartWeilRestriction R₀ B₀ Y
  let : IsSeparated Y.hom := isSeparated_of_projectiveImmersion B₀ Y n j hj
  have hp : (p.changeRing (numberFieldLevelFactorAlgEquiv K S₀).toAlgHom).changeRing
      (Pi.evalAlgHom R₀ C₀ i) =
        p.changeRing (numberFieldLevelFactorAlgHom K S₀ i) := by
    change ringTestMap R₀ (Pi.evalAlgHom R₀ C₀ i) ≫
      (ringTestMap R₀ (numberFieldLevelFactorAlgEquiv K S₀).toAlgHom ≫ p) = _
    rw [← Category.assoc, ← ringTestMap_comp]
    rfl
  change productTensorWeilPointEquiv R₀ B₀ C₀
    (Above K L S) (upperFactor K L S) (tensorEquiv K L S)
    (tensorEquiv_one_tmul K L S) Y
    (hasFiniteAffineNeighborhoods_of_projectiveImmersion B₀ n j)
    (p.changeRing (numberFieldLevelFactorAlgEquiv K S₀).toAlgHom) ⟨i, q⟩ = _
  rw [productTensorWeilPointEquiv_local, hp]

end Langlands.Global.NumberFieldSIntegerLevelWeil
