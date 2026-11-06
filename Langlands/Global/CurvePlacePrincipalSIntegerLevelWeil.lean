import Langlands.AlgebraicGeometry.PointTopology.ProductTensorWeilTopology
import Langlands.AlgebraicGeometry.PointTopology.CurvePlacePrincipalSIntegerModelCompatibility

noncomputable section

universe u

open CategoryTheory Topology IsDedekindDomain IntermediateField AlgebraicCurve
open _root_.AlgebraicGeometry
open scoped TensorProduct AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global Langlands.Global.CurvePlacePrincipalSIntegers
  Langlands.Global.CurvePlacePrincipalSIntegerLocalTensor
  Langlands.Global.CurvePlaceCompletionExtension
  Langlands.Global.CurvePlaceCompletedIntegersExtension
  Langlands.Global.CurvePlaceIntegralTopology

namespace Langlands.Global.CurvePlacePrincipalSIntegerLevelWeil

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L] (s : K) [FiniteDimensional k⟮s⟯ K]
  (t : CurveModel.chartRing k ({s} : Set K)) [Fact (t ≠ 0)]

/-- The original lower place underlying a field or integer level coordinate. -/
def lowerPlace :
    CurvePlaceLevelFactorIndex k K (curvePlacePrincipalExceptional k K s (t : K)) → Place k K
  | .inl p => p.1
  | .inr p => p.1

/-- All original upper places above a given lower level coordinate. -/
abbrev Above
    (i : CurvePlaceLevelFactorIndex k K (curvePlacePrincipalExceptional k K s (t : K))) :=
  CurvePlacesAbove k L (lowerPlace k K s t i)

/-- The actual upper field or completed integer ring belonging to an original level coordinate. -/
def upperFactor
    (i : CurvePlaceLevelFactorIndex k K (curvePlacePrincipalExceptional k K s (t : K))) :
    Above k K L s t i → Type u :=
  match i with
  | .inl _ => fun q => curvePlaceCompletion q.1
  | .inr _ => fun q => curvePlaceCompletionIntegers q.1

scoped instance upperCommRing (i) (q : Above k K L s t i) :
    CommRing (upperFactor k K L s t i q) := by
  cases i <;> dsimp [upperFactor] <;> infer_instance

scoped instance upperTopology (i) (q : Above k K L s t i) :
    TopologicalSpace (upperFactor k K L s t i q) := by
  cases i <;> dsimp [upperFactor] <;> infer_instance

scoped instance upperTopologicalRing (i) (q : Above k K L s t i) :
    IsTopologicalRing (upperFactor k K L s t i q) := by
  cases i <;> dsimp [upperFactor] <;> infer_instance

scoped instance upperLocalRing (i) (q : Above k K L s t i) :
    IsLocalRing (upperFactor k K L s t i q) := by
  cases i <;> dsimp [upperFactor] <;> infer_instance

scoped instance upperOpenUnits (i) (q : Above k K L s t i) :
    IsOpenUnits (upperFactor k K L s t i q) := by
  cases i <;> dsimp [upperFactor] <;> infer_instance

scoped instance lowerOpenUnits
    (i : CurvePlaceLevelFactorIndex k K (curvePlacePrincipalExceptional k K s (t : K))) :
    IsOpenUnits
      (CurvePlaceLevelFactor k K (curvePlacePrincipalExceptional k K s (t : K)) i) := by
  cases i <;> dsimp [CurvePlaceLevelFactor] <;> infer_instance

scoped instance upperCoefficientAlgebra (i) (q : Above k K L s t i) :
    Algebra
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K))))
      (upperFactor k K L s t i q) := by
  cases i with
  | inl p =>
    exact inferInstanceAs (Algebra
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K)))) (curvePlaceCompletion q.1))
  | inr p =>
    letI : Fact (p.1 ∉ curvePlacePrincipalExceptional k K s (t : K)) := ⟨p.2⟩
    exact CurvePlacePrincipalSIntegerLocalTensor.upperCompletedAlgebra k K s t p.1 L q

scoped instance lowerFactorAlgebra (i) (q : Above k K L s t i) :
    Algebra (CurvePlaceLevelFactor k K (curvePlacePrincipalExceptional k K s (t : K)) i)
      (upperFactor k K L s t i q) := by
  cases i <;> dsimp [CurvePlaceLevelFactor, upperFactor] <;> infer_instance

scoped instance localFinite (i) (q : Above k K L s t i) :
    Module.Finite
      (CurvePlaceLevelFactor k K (curvePlacePrincipalExceptional k K s (t : K)) i)
      (upperFactor k K L s t i q) := by
  cases i with
  | inl p => exact CurvePlaceCompletionExtension.localFinite p.1 q
  | inr p => exact CurvePlaceIntegralTopology.localFinite p.1 q

scoped instance localProjective (i) (q : Above k K L s t i) :
    Module.Projective
      (CurvePlaceLevelFactor k K (curvePlacePrincipalExceptional k K s (t : K)) i)
      (upperFactor k K L s t i q) := by
  cases i with
  | inl p =>
    change Module.Projective (curvePlaceCompletion p.1) (curvePlaceCompletion q.1)
    let : Module.Free (curvePlaceCompletion p.1) (curvePlaceCompletion q.1) :=
      Module.Free.of_divisionRing _ _
    exact Module.Projective.of_free
  | inr p => exact CurvePlaceIntegralTopology.localProjective p.1 q

scoped instance localModuleTopology (i) (q : Above k K L s t i) :
    IsModuleTopology
      (CurvePlaceLevelFactor k K (curvePlacePrincipalExceptional k K s (t : K)) i)
      (upperFactor k K L s t i q) := by
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

/-- Every actual level coordinate has its proved original completed-field or completed-integer tensor. -/
def tensorEquiv
    (i : CurvePlaceLevelFactorIndex k K (curvePlacePrincipalExceptional k K s (t : K))) :
    CurvePlaceLevelFactor k K (curvePlacePrincipalExceptional k K s (t : K)) i ⊗[
      curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))]
      (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
        (curvePlacePrincipalExceptional k K s (t : K)))) ≃ₐ[
      CurvePlaceLevelFactor k K (curvePlacePrincipalExceptional k K s (t : K)) i]
      (∀ q : Above k K L s t i, upperFactor k K L s t i q) := by
  cases i with
  | inl p => exact CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv k K L s t p.1
  | inr p =>
    letI : Fact (p.1 ∉ curvePlacePrincipalExceptional k K s (t : K)) := ⟨p.2⟩
    exact CurvePlacePrincipalSIntegerLocalTensor.completedTensorEquiv k K s t p.1 L

@[simp]
theorem tensorEquiv_one_tmul
    (i : CurvePlaceLevelFactorIndex k K (curvePlacePrincipalExceptional k K s (t : K)))
    (b : curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (t : K)))) (q : Above k K L s t i) :
    tensorEquiv k K L s t i
      (1 ⊗ₜ[curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))] b) q =
      algebraMap
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K))))
        (upperFactor k K L s t i q) b := by
  cases i with
  | inl p => exact CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv_one_tmul k K L s t p.1 b q
  | inr p =>
    let : Fact (p.1 ∉ curvePlacePrincipalExceptional k K s (t : K)) := ⟨p.2⟩
    exact CurvePlacePrincipalSIntegerLocalTensor.completedTensorEquiv_one_tmul k K s t p.1 L b q

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

/-- Actual lower adelic-level Weil points have the product topology of every original upper local factor. -/
def levelPointHomeomorph :
    letI : TopologicalSpace
        (RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
          (affineChartWeilRestriction
            (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) _ Y)
          (curvePlaceAdeleLevel k K (curvePlacePrincipalExceptional k K s (t : K)))) :=
      curvePlaceLevelModelPointTopology k K (curvePlacePrincipalExceptional k K s (t : K))
        (affineChartWeilRestriction
          (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) _ Y)
    letI : ∀ z : Σ i, Above k K L s t i, TopologicalSpace
        (RingPoint
          (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
            (curvePlacePrincipalExceptional k K s (t : K)))) Y
          (upperFactor k K L s t z.1 z.2)) :=
      fun z => schemePointTopology
        (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
          (curvePlacePrincipalExceptional k K s (t : K)))) Y
        (upperFactor k K L s t z.1 z.2)
    RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
        (affineChartWeilRestriction
          (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) _ Y)
        (curvePlaceAdeleLevel k K (curvePlacePrincipalExceptional k K s (t : K))) ≃ₜ
      (∀ z : Σ i, Above k K L s t i,
        RingPoint
          (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
            (curvePlacePrincipalExceptional k K s (t : K)))) Y
          (upperFactor k K L s t z.1 z.2)) := by
  let R₀ := curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))
  let B₀ := curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
    (curvePlacePrincipalExceptional k K s (t : K)))
  let S₀ := curvePlacePrincipalExceptional k K s (t : K)
  let C₀ := CurvePlaceLevelFactor k K S₀
  let W := affineChartWeilRestriction R₀ B₀ Y
  letI := isSeparated_of_projectiveImmersion B₀ Y n j hj
  letI : TopologicalSpace (RingPoint R₀ W (curvePlaceAdeleLevel k K S₀)) :=
    curvePlaceLevelModelPointTopology k K S₀ W
  letI : TopologicalSpace (RingPoint R₀ W (∀ i, C₀ i)) :=
    localProductPointTopology R₀ C₀ W
  letI : ∀ z : Σ i, Above k K L s t i,
      TopologicalSpace (RingPoint B₀ Y (upperFactor k K L s t z.1 z.2)) :=
    fun z => schemePointTopology B₀ Y (upperFactor k K L s t z.1 z.2)
  let E := ringPointChangeRingEquiv R₀ W (curvePlaceLevelFactorAlgEquiv k K S₀)
  have hind : IsInducing (E : _ → _) :=
    ⟨curvePlaceLevelModelPointTopology_eq k K S₀ W⟩
  let H := IsHomeomorph.homeomorph E
    (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨⟨hind, E.injective⟩, E.surjective⟩)
  exact H.trans (productTensorWeilPointHomeomorph R₀ B₀ C₀
    (Above k K L s t) (upperFactor k K L s t) (tensorEquiv k K L s t)
    (tensorEquiv_one_tmul k K L s t) Y
    (hasFiniteAffineNeighborhoods_of_projectiveImmersion B₀ n j))

/-- Each level component is the original local Weil map after the literal original level projection. -/
theorem levelPointHomeomorph_component
    (p : RingPoint (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K)))
      (affineChartWeilRestriction
        (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) _ Y)
      (curvePlaceAdeleLevel k K (curvePlacePrincipalExceptional k K s (t : K))))
    (i : CurvePlaceLevelFactorIndex k K (curvePlacePrincipalExceptional k K s (t : K)))
    (q : Above k K L s t i) :
    levelPointHomeomorph k K L s t Y n j hj p ⟨i, q⟩ =
      completedTensorWeilRestrictionPointMap
        (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) _
        (CurvePlaceLevelFactor k K (curvePlacePrincipalExceptional k K s (t : K)) i)
        (upperFactor k K L s t i) (tensorEquiv k K L s t i)
        (tensorEquiv_one_tmul k K L s t i) Y
        (p.changeRing (curvePlaceLevelFactorAlgHom k K
          (curvePlacePrincipalExceptional k K s (t : K)) i)) q := by
  let R₀ := curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))
  let B₀ := curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
    (curvePlacePrincipalExceptional k K s (t : K)))
  let S₀ := curvePlacePrincipalExceptional k K s (t : K)
  let C₀ := CurvePlaceLevelFactor k K S₀
  let W := affineChartWeilRestriction R₀ B₀ Y
  let : IsSeparated Y.hom := isSeparated_of_projectiveImmersion B₀ Y n j hj
  have hp : (p.changeRing (curvePlaceLevelFactorAlgEquiv k K S₀).toAlgHom).changeRing
      (Pi.evalAlgHom R₀ C₀ i) =
        p.changeRing (curvePlaceLevelFactorAlgHom k K S₀ i) := by
    change ringTestMap R₀ (Pi.evalAlgHom R₀ C₀ i) ≫
      (ringTestMap R₀ (curvePlaceLevelFactorAlgEquiv k K S₀).toAlgHom ≫ p) = _
    rw [← Category.assoc, ← ringTestMap_comp]
    rfl
  change productTensorWeilPointEquiv R₀ B₀ C₀
    (Above k K L s t) (upperFactor k K L s t) (tensorEquiv k K L s t)
    (tensorEquiv_one_tmul k K L s t) Y
    (hasFiniteAffineNeighborhoods_of_projectiveImmersion B₀ n j)
    (p.changeRing (curvePlaceLevelFactorAlgEquiv k K S₀).toAlgHom) ⟨i, q⟩ = _
  rw [productTensorWeilPointEquiv_local, hp]

end Langlands.Global.CurvePlacePrincipalSIntegerLevelWeil
