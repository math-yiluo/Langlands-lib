import Langlands.Global.NumberFieldSIntegerLevelWeil
import Langlands.Global.AdelicFixedModelLocalProductTopology

noncomputable section

universe u

open CategoryTheory Topology IsDedekindDomain
open _root_.AlgebraicGeometry
open scoped NumberField TensorProduct NumberField.LiesOver
  Langlands.Global Langlands.Global.NumberFieldSIntegers
  Langlands.Global.NumberFieldSIntegerLocalTensor
  Langlands.Global.NumberFieldSIntegerLevelWeil
  Langlands.Global.FixedModelLocalProduct
  Langlands.Global.AdelicFunctoriality.FiniteExtension
  Langlands.Global.AdelicFunctoriality.InfiniteExtension
  Langlands.Global.AdelicFunctoriality.IntegralTensor
  Langlands.Global.AdelicFunctoriality.IntegralTopology

namespace Langlands.Global.NumberFieldSIntegerFixedLevelWeil

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open AdelicFunctoriality NumberFieldSIntegerLevelWeil

set_option backward.isDefEq.respectTransparency false

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (S : Finset (FinitePlace K)) (T : AdelicLevelIndexAbove S)

/-- Restrict the original upper coefficients at the fixed base support to every enlarged-level factor. -/
scoped instance upperCoefficientAlgebra (i) (q : Above K L T.val i) :
    Algebra (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L) (upperFactor K L T.val i q) := by
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
      letI : Fact (p.1 ∉ S) := ⟨fun h => p.2 (T.property h)⟩
      exact NumberFieldSIntegerLocalTensor.upperCompletedAlgebra K S p.1 L q

private def tensorData (i : NumberFieldLevelFactorIndex K T.val) :
    { e : NumberFieldLevelFactor K T.val i ⊗[(S : Set (FinitePlace K)).integer K]
        (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
          Set (FinitePlace L)).integer L) ≃ₐ[NumberFieldLevelFactor K T.val i]
        (∀ q : Above K L T.val i, upperFactor K L T.val i q) //
      ∀ (b : (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
          Set (FinitePlace L)).integer L)) (q : Above K L T.val i),
        e (1 ⊗ₜ[(S : Set (FinitePlace K)).integer K] b) q =
          algebraMap (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
            Set (FinitePlace L)).integer L) (upperFactor K L T.val i q) b } := by
  cases i with
  | inl p =>
    have h : FixedModelLocalProduct.numberFieldFactorAlgebra K S T (.inl p) =
        Subalgebra.toAlgebra (α := p.Completion) ((S : Set (FinitePlace K)).integer K) :=
      Algebra.algebra_ext _ _ fun _ => rfl
    rw [h]
    exact ⟨NumberFieldSIntegerInfiniteTensor.tensorEquiv K L S p,
      NumberFieldSIntegerInfiniteTensor.tensorEquiv_one_tmul K L S p⟩
  | inr z =>
    cases z with
    | inl p =>
      have h : FixedModelLocalProduct.numberFieldFactorAlgebra K S T (.inr (.inl p)) =
          Subalgebra.toAlgebra (α := p.1.adicCompletion K) ((S : Set (FinitePlace K)).integer K) :=
        Algebra.algebra_ext _ _ fun _ => rfl
      rw [h]
      exact ⟨NumberFieldSIntegerFieldTensor.tensorEquiv K L S p.1,
        NumberFieldSIntegerFieldTensor.tensorEquiv_one_tmul K L S p.1⟩
    | inr p =>
      letI : Fact (p.1 ∉ S) := ⟨fun h => p.2 (T.property h)⟩
      have h : FixedModelLocalProduct.numberFieldFactorAlgebra K S T (.inr (.inr p)) =
          NumberFieldSIntegerLocalTensor.completedAlgebra K S p.1 :=
        Algebra.algebra_ext _ _ fun _ => rfl
      rw [h]
      exact ⟨NumberFieldSIntegerLocalTensor.completedTensorEquiv K S p.1 L,
        NumberFieldSIntegerLocalTensor.completedTensorEquiv_one_tmul K S p.1 L⟩

/-- Tensor the original fixed S-integer coefficients with every factor of an arbitrary enlarged level. -/
def tensorEquiv (i : NumberFieldLevelFactorIndex K T.val) :
    NumberFieldLevelFactor K T.val i ⊗[(S : Set (FinitePlace K)).integer K]
      (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
        Set (FinitePlace L)).integer L) ≃ₐ[NumberFieldLevelFactor K T.val i]
      (∀ q : Above K L T.val i, upperFactor K L T.val i q) :=
  (tensorData K L S T i).1

@[simp]
theorem tensorEquiv_one_tmul (i : NumberFieldLevelFactorIndex K T.val)
    (b : (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
      Set (FinitePlace L)).integer L)) (q : Above K L T.val i) :
    tensorEquiv K L S T i (1 ⊗ₜ[(S : Set (FinitePlace K)).integer K] b) q =
      algebraMap (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
        Set (FinitePlace L)).integer L) (upperFactor K L T.val i q) b :=
  (tensorData K L S T i).2 b q

/-- The literal enlarged-level projection, with coefficients restricted to the fixed base. -/
def levelFactorAlgHom (i : NumberFieldLevelFactorIndex K T.val) :
    numberFieldAdeleLevelOver K S T →ₐ[(S : Set (FinitePlace K)).integer K]
      NumberFieldLevelFactor K T.val i :=
  (Pi.evalAlgHom ((S : Set (FinitePlace K)).integer K)
    (NumberFieldLevelFactor K T.val) i).comp
      (FixedModelLocalProduct.numberFieldFactorAlgEquiv K S T).toAlgHom

@[simp]
theorem levelFactorAlgHom_toRingHom (i : NumberFieldLevelFactorIndex K T.val) :
    (levelFactorAlgHom K S T i).toRingHom = numberFieldLevelFactorProjection K T.val i := rfl

variable
  (Y : Over (Spec (CommRingCat.of
    ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)))))
  [LocallyOfFiniteType Y.hom] [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
  (n : ℕ)
  (j : Y.left ⟶ ProjectiveSpace
    ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) n)
  [IsImmersion j]
  (hj : j ≫ projectiveSpaceToSpec
    ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) n = Y.hom)

/-- Enlarge the adelic support of the original fixed integral Weil model while
retaining the original upper coefficients and every original local factor. -/
def levelPointHomeomorph :
    letI : TopologicalSpace
        (RingPoint ((S : Set (FinitePlace K)).integer K)
          (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) _ Y)
          (numberFieldAdeleLevelOver K S T)) :=
      numberFieldFixedModelStageTopology K S
        (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) _ Y) T
    letI : ∀ z : Σ i, Above K L T.val i, TopologicalSpace
        (RingPoint
          ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) Y
          (upperFactor K L T.val z.1 z.2)) :=
      fun z => schemePointTopology
        ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) Y
        (upperFactor K L T.val z.1 z.2)
    RingPoint ((S : Set (FinitePlace K)).integer K)
        (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) _ Y)
        (numberFieldAdeleLevelOver K S T) ≃ₜ
      (∀ z : Σ i, Above K L T.val i,
        RingPoint
          ((((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)) Y
          (upperFactor K L T.val z.1 z.2)) := by
  let A := ((S : Set (FinitePlace K)).integer K)
  let B := (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)
  let C := NumberFieldLevelFactor K T.val
  let W := affineChartWeilRestriction A B Y
  letI := isSeparated_of_projectiveImmersion B Y n j hj
  letI : TopologicalSpace (RingPoint A W (numberFieldAdeleLevelOver K S T)) :=
    numberFieldFixedModelStageTopology K S W T
  letI : TopologicalSpace (RingPoint A W (∀ i, C i)) :=
    localProductPointTopology A C W
  letI : ∀ z : Σ i, Above K L T.val i,
      TopologicalSpace (RingPoint B Y (upperFactor K L T.val z.1 z.2)) :=
    fun z => schemePointTopology B Y (upperFactor K L T.val z.1 z.2)
  exact (FixedModelLocalProduct.numberFieldStageHomeomorph K S T W).trans
    (productTensorWeilPointHomeomorph A B C
      (Above K L T.val) (upperFactor K L T.val) (tensorEquiv K L S T)
      (tensorEquiv_one_tmul K L S T) Y
      (hasFiniteAffineNeighborhoods_of_projectiveImmersion B n j))

/-- Each component is the original local Weil map after the literal projection
from the enlarged level, with both integral coefficient rings fixed. -/
theorem levelPointHomeomorph_component
    (p : RingPoint ((S : Set (FinitePlace K)).integer K)
      (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) _ Y)
      (numberFieldAdeleLevelOver K S T))
    (i : NumberFieldLevelFactorIndex K T.val) (q : Above K L T.val i) :
    levelPointHomeomorph K L S T Y n j hj p ⟨i, q⟩ =
      completedTensorWeilRestrictionPointMap
        ((S : Set (FinitePlace K)).integer K) _
        (NumberFieldLevelFactor K T.val i)
        (upperFactor K L T.val i) (tensorEquiv K L S T i)
        (tensorEquiv_one_tmul K L S T i) Y
        (p.changeRing (levelFactorAlgHom K S T i)) q := by
  let A := ((S : Set (FinitePlace K)).integer K)
  let B := (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)
  let C := NumberFieldLevelFactor K T.val
  let W := affineChartWeilRestriction A B Y
  let : IsSeparated Y.hom := isSeparated_of_projectiveImmersion B Y n j hj
  have hp : (p.changeRing (FixedModelLocalProduct.numberFieldFactorAlgEquiv K S T).toAlgHom).changeRing
      (Pi.evalAlgHom A C i) = p.changeRing (levelFactorAlgHom K S T i) := by
    change ringTestMap A (Pi.evalAlgHom A C i) ≫
      (ringTestMap A (FixedModelLocalProduct.numberFieldFactorAlgEquiv K S T).toAlgHom ≫ p) = _
    rw [← Category.assoc, ← ringTestMap_comp]
    rfl
  change productTensorWeilPointEquiv A B C
    (Above K L T.val) (upperFactor K L T.val) (tensorEquiv K L S T)
    (tensorEquiv_one_tmul K L S T) Y
    (hasFiniteAffineNeighborhoods_of_projectiveImmersion B n j)
    (p.changeRing (FixedModelLocalProduct.numberFieldFactorAlgEquiv K S T).toAlgHom) ⟨i, q⟩ = _
  rw [productTensorWeilPointEquiv_local, hp]

end Langlands.Global.NumberFieldSIntegerFixedLevelWeil
