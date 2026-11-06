import Langlands.Global.CurvePlacePrincipalSIntegerLevelWeil
import Langlands.Global.AdelicFixedModelLocalProductTopology

noncomputable section

universe u

open CategoryTheory Topology IsDedekindDomain IntermediateField AlgebraicCurve
open _root_.AlgebraicGeometry
open scoped TensorProduct AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global Langlands.Global.FixedModelLocalProduct
  Langlands.Global.CurvePlacePrincipalSIntegers
  Langlands.Global.CurvePlacePrincipalSIntegerLocalTensor
  Langlands.Global.CurvePlaceCompletionExtension
  Langlands.Global.CurvePlaceCompletedIntegersExtension
  Langlands.Global.CurvePlaceIntegralTopology

namespace Langlands.Global.CurvePlacePrincipalSIntegerFixedLevelWeil

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L] (s : K) [FiniteDimensional k⟮s⟯ K]
  (t : CurveModel.chartRing k ({s} : Set K)) [Fact (t ≠ 0)]

  (T : AdelicLevelIndexAbove (curvePlacePrincipalExceptional k K s (t : K)))

/-- The original lower place underlying a field or integer level coordinate. -/
def lowerPlace :
    CurvePlaceLevelFactorIndex k K T.val → Place k K
  | .inl p => p.1
  | .inr p => p.1

/-- All original upper places above a given lower level coordinate. -/
abbrev Above
    (i : CurvePlaceLevelFactorIndex k K T.val) :=
  CurvePlacesAbove k L (lowerPlace k K s t T i)

/-- The actual upper field or completed integer ring belonging to an original level coordinate. -/
def upperFactor
    (i : CurvePlaceLevelFactorIndex k K T.val) :
    Above k K L s t T i → Type u :=
  match i with
  | .inl _ => fun q => curvePlaceCompletion q.1
  | .inr _ => fun q => curvePlaceCompletionIntegers q.1

scoped instance upperCommRing (i) (q : Above k K L s t T i) :
    CommRing (upperFactor k K L s t T i q) := by
  cases i <;> dsimp [upperFactor] <;> infer_instance

scoped instance upperTopology (i) (q : Above k K L s t T i) :
    TopologicalSpace (upperFactor k K L s t T i q) := by
  cases i <;> dsimp [upperFactor] <;> infer_instance

scoped instance upperTopologicalRing (i) (q : Above k K L s t T i) :
    IsTopologicalRing (upperFactor k K L s t T i q) := by
  cases i <;> dsimp [upperFactor] <;> infer_instance

scoped instance upperLocalRing (i) (q : Above k K L s t T i) :
    IsLocalRing (upperFactor k K L s t T i q) := by
  cases i <;> dsimp [upperFactor] <;> infer_instance

scoped instance upperOpenUnits (i) (q : Above k K L s t T i) :
    IsOpenUnits (upperFactor k K L s t T i q) := by
  cases i <;> dsimp [upperFactor] <;> infer_instance

scoped instance lowerOpenUnits
    (i : CurvePlaceLevelFactorIndex k K T.val) :
    IsOpenUnits
      (CurvePlaceLevelFactor k K T.val i) := by
  cases i <;> dsimp [CurvePlaceLevelFactor] <;> infer_instance

scoped instance upperCoefficientAlgebra (i) (q : Above k K L s t T i) :
    Algebra
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K))))
      (upperFactor k K L s t T i q) := by
  cases i with
  | inl p =>
    exact inferInstanceAs (Algebra
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceCompletion q.1))
  | inr p =>
    letI : Fact (p.1 ∉ curvePlacePrincipalExceptional k K s (t : K)) := ⟨fun h => p.2 (T.property h)⟩
    exact CurvePlacePrincipalSIntegerLocalTensor.upperCompletedAlgebra k K s t p.1 L q

scoped instance lowerFactorAlgebra (i) (q : Above k K L s t T i) :
    Algebra (CurvePlaceLevelFactor k K T.val i)
      (upperFactor k K L s t T i q) := by
  cases i <;> dsimp [CurvePlaceLevelFactor, upperFactor] <;> infer_instance

scoped instance localFinite (i) (q : Above k K L s t T i) :
    Module.Finite
      (CurvePlaceLevelFactor k K T.val i)
      (upperFactor k K L s t T i q) := by
  cases i with
  | inl p => exact CurvePlaceCompletionExtension.localFinite p.1 q
  | inr p => exact CurvePlaceIntegralTopology.localFinite p.1 q

scoped instance localProjective (i) (q : Above k K L s t T i) :
    Module.Projective
      (CurvePlaceLevelFactor k K T.val i)
      (upperFactor k K L s t T i q) := by
  cases i with
  | inl p =>
    change Module.Projective (curvePlaceCompletion p.1) (curvePlaceCompletion q.1)
    let : Module.Free (curvePlaceCompletion p.1) (curvePlaceCompletion q.1) :=
      Module.Free.of_divisionRing _ _
    exact Module.Projective.of_free
  | inr p => exact CurvePlaceIntegralTopology.localProjective p.1 q

scoped instance localModuleTopology (i) (q : Above k K L s t T i) :
    IsModuleTopology
      (CurvePlaceLevelFactor k K T.val i)
      (upperFactor k K L s t T i q) := by
  cases i with
  | inl p =>
    let : (Valued.v : Valuation (curvePlaceCompletion p.1)
        (WithZero (Multiplicative ℤ))).RankOne :=
      Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 by norm_num)
    let : NontriviallyNormedField (curvePlaceCompletion p.1) :=
      Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
    change IsModuleTopology (curvePlaceCompletion p.1) (curvePlaceCompletion q.1)
    exact isModuleTopologyOfFiniteDimensional
  | inr p => exact CurvePlaceIntegralTopology.moduleTopology p.1 q

private def tensorData (i : CurvePlaceLevelFactorIndex k K T.val) :
    { e : CurvePlaceLevelFactor k K T.val i ⊗[
        curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))]
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) ≃ₐ[CurvePlaceLevelFactor k K T.val i]
        (∀ q : Above k K L s t T i, upperFactor k K L s t T i q) //
      ∀ (b : curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) (q : Above k K L s t T i),
        e (1 ⊗ₜ[curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))] b) q =
          algebraMap (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
            (curvePlacePrincipalExceptional k K s (t : K)))) (upperFactor k K L s t T i q) b } := by
  cases i with
  | inl p =>
    have h : FixedModelLocalProduct.curveFactorAlgebra k K
        (curvePlacePrincipalExceptional k K s (t : K)) T (.inl p) =
        inferInstanceAs (Algebra
          (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
          (curvePlaceCompletion p.1)) :=
      Algebra.algebra_ext _ _ fun _ => rfl
    rw [h]
    exact ⟨CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv k K L s t p.1,
      CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv_one_tmul k K L s t p.1⟩
  | inr p =>
    letI : Fact (p.1 ∉ curvePlacePrincipalExceptional k K s (t : K)) :=
      ⟨fun h => p.2 (T.property h)⟩
    have h : FixedModelLocalProduct.curveFactorAlgebra k K
        (curvePlacePrincipalExceptional k K s (t : K)) T (.inr p) =
        CurvePlacePrincipalSIntegerLocalTensor.completedAlgebra k K s t p.1 :=
      Algebra.algebra_ext _ _ fun _ => rfl
    rw [h]
    exact ⟨CurvePlacePrincipalSIntegerLocalTensor.completedTensorEquiv k K s t p.1 L,
      CurvePlacePrincipalSIntegerLocalTensor.completedTensorEquiv_one_tmul k K s t p.1 L⟩

/-- Tensor the original principal S-integer coefficients at every enlarged-support coordinate. -/
def tensorEquiv (i : CurvePlaceLevelFactorIndex k K T.val) :
    CurvePlaceLevelFactor k K T.val i ⊗[
      curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))]
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K)))) ≃ₐ[CurvePlaceLevelFactor k K T.val i]
      (∀ q : Above k K L s t T i, upperFactor k K L s t T i q) :=
  (tensorData k K L s t T i).1

@[simp]
theorem tensorEquiv_one_tmul (i : CurvePlaceLevelFactorIndex k K T.val)
    (b : curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (q : Above k K L s t T i) :
    tensorEquiv k K L s t T i
      (1 ⊗ₜ[curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))] b) q =
      algebraMap (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K)))) (upperFactor k K L s t T i q) b :=
  (tensorData k K L s t T i).2 b q

/-- The literal enlarged-level projection as a map over the original principal base. -/
def levelFactorAlgHom (i : CurvePlaceLevelFactorIndex k K T.val) :
    curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T →ₐ[
      curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))]
      CurvePlaceLevelFactor k K T.val i :=
  (Pi.evalAlgHom (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
    (CurvePlaceLevelFactor k K T.val) i).comp
      (FixedModelLocalProduct.curveFactorAlgEquiv k K
        (curvePlacePrincipalExceptional k K s (t : K)) T).toAlgHom

omit [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)] in
@[simp]
theorem levelFactorAlgHom_toRingHom (i : CurvePlaceLevelFactorIndex k K T.val) :
    (levelFactorAlgHom k K s t T i).toRingHom =
      curvePlaceLevelFactorProjection k K T.val i := rfl

variable
  (Y : Over (Spec (CommRingCat.of
    (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))))))
  [LocallyOfFiniteType Y.hom] [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
  (n : ℕ)
  (j : Y.left ⟶ ProjectiveSpace
    (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) n) [IsImmersion j]
  (hj : j ≫ projectiveSpaceToSpec
    (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) n = Y.hom)

/-- Enlarge the support of the original integral curve Weil model while retaining
its original principal coefficients and every original upper local factor. -/
def levelPointHomeomorph :
    letI : TopologicalSpace
        (RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
          (affineChartWeilRestriction
            (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) _ Y)
          (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)) :=
      curvePlaceFixedModelStageTopology k K (curvePlacePrincipalExceptional k K s (t : K))
        (affineChartWeilRestriction
          (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) _ Y) T
    letI : ∀ z : Σ i, Above k K L s t T i, TopologicalSpace
        (RingPoint
          (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
            (curvePlacePrincipalExceptional k K s (t : K)))) Y
          (upperFactor k K L s t T z.1 z.2)) :=
      fun z => schemePointTopology
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) Y
        (upperFactor k K L s t T z.1 z.2)
    RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
        (affineChartWeilRestriction
          (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) _ Y)
        (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T) ≃ₜ
      (∀ z : Σ i, Above k K L s t T i,
        RingPoint
          (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
            (curvePlacePrincipalExceptional k K s (t : K)))) Y
          (upperFactor k K L s t T z.1 z.2)) := by
  let A := curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))
  let B := curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
    (curvePlacePrincipalExceptional k K s (t : K)))
  let C := CurvePlaceLevelFactor k K T.val
  let W := affineChartWeilRestriction A B Y
  letI := isSeparated_of_projectiveImmersion B Y n j hj
  letI : TopologicalSpace (RingPoint A W
      (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)) :=
    curvePlaceFixedModelStageTopology k K (curvePlacePrincipalExceptional k K s (t : K)) W T
  letI : TopologicalSpace (RingPoint A W (∀ i, C i)) :=
    localProductPointTopology A C W
  letI : ∀ z : Σ i, Above k K L s t T i,
      TopologicalSpace (RingPoint B Y (upperFactor k K L s t T z.1 z.2)) :=
    fun z => schemePointTopology B Y (upperFactor k K L s t T z.1 z.2)
  exact (FixedModelLocalProduct.curveStageHomeomorph k K
    (curvePlacePrincipalExceptional k K s (t : K)) T W).trans
      (productTensorWeilPointHomeomorph A B C
        (Above k K L s t T) (upperFactor k K L s t T) (tensorEquiv k K L s t T)
        (tensorEquiv_one_tmul k K L s t T) Y
        (hasFiniteAffineNeighborhoods_of_projectiveImmersion B n j))

/-- Every component is the original local Weil counit after the literal projection
from the enlarged support, over the two original integral bases. -/
theorem levelPointHomeomorph_component
    (p : RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
      (affineChartWeilRestriction
        (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) _ Y)
      (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T))
    (i : CurvePlaceLevelFactorIndex k K T.val) (q : Above k K L s t T i) :
    levelPointHomeomorph k K L s t T Y n j hj p ⟨i, q⟩ =
      completedTensorWeilRestrictionPointMap
        (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) _
        (CurvePlaceLevelFactor k K T.val i)
        (upperFactor k K L s t T i) (tensorEquiv k K L s t T i)
        (tensorEquiv_one_tmul k K L s t T i) Y
        (p.changeRing (levelFactorAlgHom k K s t T i)) q := by
  let A := curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))
  let B := curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
    (curvePlacePrincipalExceptional k K s (t : K)))
  let C := CurvePlaceLevelFactor k K T.val
  let W := affineChartWeilRestriction A B Y
  let : IsSeparated Y.hom := isSeparated_of_projectiveImmersion B Y n j hj
  have hp : (p.changeRing (FixedModelLocalProduct.curveFactorAlgEquiv k K
      (curvePlacePrincipalExceptional k K s (t : K)) T).toAlgHom).changeRing
      (Pi.evalAlgHom A C i) = p.changeRing (levelFactorAlgHom k K s t T i) := by
    change ringTestMap A (Pi.evalAlgHom A C i) ≫
      (ringTestMap A (FixedModelLocalProduct.curveFactorAlgEquiv k K
        (curvePlacePrincipalExceptional k K s (t : K)) T).toAlgHom ≫ p) = _
    rw [← Category.assoc, ← ringTestMap_comp]
    rfl
  change productTensorWeilPointEquiv A B C
    (Above k K L s t T) (upperFactor k K L s t T) (tensorEquiv k K L s t T)
    (tensorEquiv_one_tmul k K L s t T) Y
    (hasFiniteAffineNeighborhoods_of_projectiveImmersion B n j)
    (p.changeRing (FixedModelLocalProduct.curveFactorAlgEquiv k K
      (curvePlacePrincipalExceptional k K s (t : K)) T).toAlgHom) ⟨i, q⟩ = _
  rw [productTensorWeilPointEquiv_local, hp]

end Langlands.Global.CurvePlacePrincipalSIntegerFixedLevelWeil
