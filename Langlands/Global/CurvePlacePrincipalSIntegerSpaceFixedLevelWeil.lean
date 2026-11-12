import Langlands.Global.CurvePlacePrincipalSIntegerSpaceWeilTopology
import Langlands.Global.CurvePlaceSpaceStageCoordinates
import Langlands.Global.CurvePlacePrincipalSIntegerFixedLevelWeil

/-! # Fixed-model curve-place stages and original local Weil factors -/

noncomputable section

universe u

open CategoryTheory Topology IsDedekindDomain IntermediateField AlgebraicCurve
open _root_.AlgebraicGeometry
open scoped TensorProduct AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global Langlands.Global.FixedModelLocalProduct
  Langlands.Global.AdelicSpaceStageCoordinates
  Langlands.Global.CurvePlacePrincipalSIntegers
  Langlands.Global.CurvePlacePrincipalSIntegerLocalTensor
  Langlands.Global.CurvePlacePrincipalSIntegerFieldTensor
  Langlands.Global.CurvePlacePrincipalSIntegerFixedLevelWeil
  Langlands.Global.CurvePlaceCompletionExtension
  Langlands.Global.CurvePlaceCompletedIntegersExtension
  Langlands.Global.CurvePlaceIntegralTopology

namespace Langlands.Global.CurvePlacePrincipalSIntegerSpaceFixedLevelWeil

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology
open CurvePlacePrincipalSIntegerFixedLevelWeil
open CurvePlacePrincipalSIntegerSpaceWeilTopology (lowerCoefficients upperCoefficients)

set_option backward.isDefEq.respectTransparency false

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L] (s : K) [FiniteDimensional k⟮s⟯ K]
  (t : CurveModel.chartRing k ({s} : Set K)) [Fact (t ≠ 0)]
  (T : AdelicLevelIndexAbove (curvePlacePrincipalExceptional k K s (t : K)))

/-- The original field containing each upper enlarged-level factor. -/
abbrev upperField (i : CurvePlaceLevelFactorIndex k K T.val) (q : Above k K L s t T i) :=
  curvePlaceCompletion q.1

/-- The original identity or integral inclusion on each upper factor. -/
def upperFieldAlgHom (i : CurvePlaceLevelFactorIndex k K T.val) (q : Above k K L s t T i) :
    upperFactor k K L s t T i q →ₐ[upperCoefficients k K L s t] upperField k K L s t T i q := by
  cases i with
  | inl p => exact AlgHom.id _ _
  | inr p =>
    letI : Fact (p.1 ∉ curvePlacePrincipalExceptional k K s (t : K)) :=
      ⟨fun hp => p.2 (T.property hp)⟩
    letI : Algebra (upperCoefficients k K L s t) (curvePlaceCompletionIntegers q.1) :=
      CurvePlacePrincipalSIntegerLocalTensor.upperCompletedAlgebra k K s t p.1 L q
    letI : IsScalarTower (upperCoefficients k K L s t) (curvePlaceCompletionIntegers q.1)
        (curvePlaceCompletion q.1) := .of_algebraMap_eq fun _ => rfl
    exact Algebra.algHom (upperCoefficients k K L s t) (curvePlaceCompletionIntegers q.1)
      (curvePlaceCompletion q.1)

scoped instance lowerFieldNormed (i : CurvePlaceLevelFactorIndex k K T.val) :
    NontriviallyNormedField (CurvePlaceLevelField k K T.val i) := by
  cases i <;> exact AdelicSpaceLocalFields.normedField _ K _

scoped instance upperFieldNormed (i) (q : Above k K L s t T i) :
    NontriviallyNormedField (upperField k K L s t T i q) :=
  AdelicSpaceLocalFields.normedField q.1.toValuationSubring L q.1.heightOneSpectrum

scoped instance fieldFactorAlgebra (i) (q : Above k K L s t T i) :
    Algebra (CurvePlaceLevelField k K T.val i) (upperField k K L s t T i q) := by
  cases i <;> exact inferInstanceAs (Algebra (curvePlaceCompletion _) (curvePlaceCompletion q.1))

scoped instance fieldFactorContinuousSMul (i) (q : Above k K L s t T i) :
    ContinuousSMul (CurvePlaceLevelField k K T.val i) (upperField k K L s t T i q) := by
  cases i <;> exact inferInstanceAs (ContinuousSMul (curvePlaceCompletion _) (curvePlaceCompletion q.1))

scoped instance fieldFactorFinite (i) (q : Above k K L s t T i) :
    FiniteDimensional (CurvePlaceLevelField k K T.val i) (upperField k K L s t T i q) := by
  cases i <;> exact CurvePlaceCompletionExtension.localFinite _ q

scoped instance lowerFieldComplete (i : CurvePlaceLevelFactorIndex k K T.val) :
    CompleteSpace (CurvePlaceLevelField k K T.val i) := by
  cases i <;> change CompleteSpace (curvePlaceCompletion _) <;> infer_instance

scoped instance fieldFactorModuleTopology (i) (q : Above k K L s t T i) :
    IsModuleTopology (CurvePlaceLevelField k K T.val i) (upperField k K L s t T i q) := by
  cases i <;> exact isModuleTopologyOfFiniteDimensional

omit [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)] in
/-- Henselianity of the original lower completed fields. -/
theorem lowerField_henselian (i : CurvePlaceLevelFactorIndex k K T.val) :
    IsHenselianValuedField (CurvePlaceLevelField k K T.val i) := by
  cases i <;> exact AdelicSpaceLocalFields.isHenselianValuedField _ K _

omit [IsScalarTower k K L] [FiniteDimensional K L] [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)] in
/-- Henselianity of every original upper completed field. -/
theorem upperField_henselian (i) (q : Above k K L s t T i) :
    IsHenselianValuedField (upperField k K L s t T i q) :=
  AdelicSpaceLocalFields.isHenselianValuedField q.1.toValuationSubring L q.1.heightOneSpectrum

/-- Field tensor data with the original fixed-base field coefficient action. -/
def fieldTensorData (i : CurvePlaceLevelFactorIndex k K T.val) :
    { e : CurvePlaceLevelField k K T.val i ⊗[lowerCoefficients k K s t]
        upperCoefficients k K L s t ≃ₐ[CurvePlaceLevelField k K T.val i]
        (∀ q : Above k K L s t T i, upperField k K L s t T i q) //
      ∀ (b : upperCoefficients k K L s t) (q : Above k K L s t T i),
        e (1 ⊗ₜ[lowerCoefficients k K s t] b) q =
          algebraMap (upperCoefficients k K L s t) (upperField k K L s t T i q) b } := by
  cases i with
  | inl p =>
    have hF : AdelicSpaceStageCoordinates.curveFieldAlgebra k K
        (curvePlacePrincipalExceptional k K s (t : K)) T (.inl p) =
        inferInstanceAs (Algebra (lowerCoefficients k K s t) (curvePlaceCompletion p.1)) :=
      Algebra.algebra_ext _ _ fun _ => rfl
    rw [hF]
    exact ⟨CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv k K L s t p.1,
      CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv_one_tmul k K L s t p.1⟩
  | inr p =>
    have hF : AdelicSpaceStageCoordinates.curveFieldAlgebra k K
        (curvePlacePrincipalExceptional k K s (t : K)) T (.inr p) =
        inferInstanceAs (Algebra (lowerCoefficients k K s t) (curvePlaceCompletion p.1)) :=
      Algebra.algebra_ext _ _ fun _ => rfl
    rw [hF]
    exact ⟨CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv k K L s t p.1,
      CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv_one_tmul k K L s t p.1⟩

variable
  (X : AlgebraicSpace (Spec (CommRingCat.of (upperCoefficients k K L s t))))
  (h : IsAlgebraicSpace _
    ((ringWeilRestriction (lowerCoefficients k K s t) (upperCoefficients k K L s t)).obj X.toSheaf))
  (hqs : IsQuasiSeparated X) (hft : FiniteTypeOverRing (upperCoefficients k K L s t) X)

include hqs hft in
/-- The actual field tensor point comparison at every enlarged coordinate. -/
theorem fieldPointMap_isHomeomorph (i : CurvePlaceLevelFactorIndex k K T.val) :
    @IsHomeomorph _ _
      (fieldValuedPointTopology (lowerCoefficients k K s t)
        (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)
        (AlgHom.id _ (CurvePlaceLevelField k K T.val i)))
      (coordinateProductTopology (upperCoefficients k K L s t) X
        (upperField k K L s t T i) (upperField k K L s t T i) (fun _ => AlgHom.id _ _))
      (completedTensorSpaceWeilRestrictionPointMap
        (lowerCoefficients k K s t) (upperCoefficients k K L s t) (CurvePlaceLevelField k K T.val i)
        (upperField k K L s t T i) (fieldTensorData k K L s t T i).1
        (fieldTensorData k K L s t T i).2 X h) := by
  cases i with
  | inl p =>
    exact WeilRestrictionTensorTopology.isHomeomorph_completedTensorSpaceWeilRestrictionPointMap_finiteType
      (lowerCoefficients k K s t) (upperCoefficients k K L s t) (CurvePlaceLevelField k K T.val (.inl p))
      (upperField k K L s t T (.inl p)) (fieldTensorData k K L s t T (.inl p)).1
      (fieldTensorData k K L s t T (.inl p)).2 X h hqs hft
      (lowerField_henselian k K s t T (.inl p)) (upperField_henselian k K L s t T (.inl p))
  | inr p =>
    exact WeilRestrictionTensorTopology.isHomeomorph_completedTensorSpaceWeilRestrictionPointMap_finiteType
      (lowerCoefficients k K s t) (upperCoefficients k K L s t) (CurvePlaceLevelField k K T.val (.inr p))
      (upperField k K L s t T (.inr p)) (fieldTensorData k K L s t T (.inr p)).1
      (fieldTensorData k K L s t T (.inr p)).2 X h hqs hft
      (lowerField_henselian k K s t T (.inr p)) (upperField_henselian k K L s t T (.inr p))

/-- Every original lower local factor identifies homeomorphically with
its original upper factors, over the fixed S-integer model. -/
def factorPointHomeomorph (i : CurvePlaceLevelFactorIndex k K T.val) :
    letI : TopologicalSpace
        (RingPoints (lowerCoefficients k K s t)
          (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)
          (CurvePlaceLevelFactor k K T.val i)) :=
      fieldValuedPointTopology (lowerCoefficients k K s t) _
        ((curvePlaceLevelFieldAlgHom k K T.val i).restrictScalars _)
    letI : ∀ q : Above k K L s t T i, TopologicalSpace
        (RingPoints (upperCoefficients k K L s t) X (upperFactor k K L s t T i q)) :=
      fun q => fieldValuedPointTopology (upperCoefficients k K L s t) X
        (upperFieldAlgHom k K L s t T i q)
    RingPoints (lowerCoefficients k K s t)
        (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)
        (CurvePlaceLevelFactor k K T.val i) ≃ₜ
      (∀ q : Above k K L s t T i,
        RingPoints (upperCoefficients k K L s t) X (upperFactor k K L s t T i q)) := by
  have hfg : ∀ (c : CurvePlaceLevelFactor k K T.val i) (q : Above k K L s t T i),
      upperFieldAlgHom k K L s t T i q
          (algebraMap (CurvePlaceLevelFactor k K T.val i) (upperFactor k K L s t T i q) c) =
        algebraMap (CurvePlaceLevelField k K T.val i) (upperField k K L s t T i q)
          (((curvePlaceLevelFieldAlgHom k K T.val i).restrictScalars (lowerCoefficients k K s t)) c) := by
    intro c q
    cases i <;> rfl
  exact WeilRestrictionTensorTopology.integralPointHomeomorph
    (lowerCoefficients k K s t) (upperCoefficients k K L s t)
    (CurvePlaceLevelFactor k K T.val i) (CurvePlaceLevelField k K T.val i)
    (upperFactor k K L s t T i) (upperField k K L s t T i)
    (CurvePlacePrincipalSIntegerFixedLevelWeil.tensorEquiv k K L s t T i)
    (CurvePlacePrincipalSIntegerFixedLevelWeil.tensorEquiv_one_tmul k K L s t T i)
    (fieldTensorData k K L s t T i).1 (fieldTensorData k K L s t T i).2
    ((curvePlaceLevelFieldAlgHom k K T.val i).restrictScalars _)
    (upperFieldAlgHom k K L s t T i) hfg X h
    (fieldPointMap_isHomeomorph k K L s t T X h hqs hft i)

@[simp]
theorem factorPointHomeomorph_apply (i : CurvePlaceLevelFactorIndex k K T.val)
    (x : RingPoints (lowerCoefficients k K s t)
      (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)
      (CurvePlaceLevelFactor k K T.val i)) (q : Above k K L s t T i) :
    factorPointHomeomorph k K L s t T X h hqs hft i x q =
      completedTensorSpaceWeilRestrictionPointMap (lowerCoefficients k K s t) (upperCoefficients k K L s t)
        (CurvePlaceLevelFactor k K T.val i) (upperFactor k K L s t T i)
        (CurvePlacePrincipalSIntegerFixedLevelWeil.tensorEquiv k K L s t T i)
        (CurvePlacePrincipalSIntegerFixedLevelWeil.tensorEquiv_one_tmul k K L s t T i) X h x q := by
  simp only [factorPointHomeomorph, WeilRestrictionTensorTopology.integralPointHomeomorph_apply]

variable
  (hWsep : IsSeparated
    (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h))
  (hWft : FiniteTypeOverRing (lowerCoefficients k K s t)
    (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h))

variable (hS : (curvePlacePrincipalExceptional k K s (t : K)).Nonempty)

/-- Every stage of the fixed original Weil model has the product topology
of its original upper local factors, including completed valuation rings. -/
def levelPointHomeomorph :
    letI := curvePlaceSpaceStageTopology k K (curvePlacePrincipalExceptional k K s (t : K))
      (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h) T
    letI : ∀ z : Σ i, Above k K L s t T i, TopologicalSpace
        (RingPoints (upperCoefficients k K L s t) X (upperFactor k K L s t T z.1 z.2)) :=
      fun z => fieldValuedPointTopology (upperCoefficients k K L s t) X
        (upperFieldAlgHom k K L s t T z.1 z.2)
    RingPoints (lowerCoefficients k K s t)
        (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)
        (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T) ≃ₜ
      (∀ z : Σ i, Above k K L s t T i,
        RingPoints (upperCoefficients k K L s t) X (upperFactor k K L s t T z.1 z.2)) := by
  let W := ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h
  let : TopologicalSpace (RingPoints (lowerCoefficients k K s t) W (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)) :=
    curvePlaceSpaceStageTopology k K (curvePlacePrincipalExceptional k K s (t : K)) W T
  let (i : CurvePlaceLevelFactorIndex k K T.val) :
      TopologicalSpace (RingPoints (lowerCoefficients k K s t) W (CurvePlaceLevelFactor k K T.val i)) :=
    fieldValuedPointTopology (lowerCoefficients k K s t) W
      ((curvePlaceLevelFieldAlgHom k K T.val i).restrictScalars _)
  let (i : CurvePlaceLevelFactorIndex k K T.val) (q : Above k K L s t T i) :
      TopologicalSpace (RingPoints (upperCoefficients k K L s t) X (upperFactor k K L s t T i q)) :=
    fieldValuedPointTopology (upperCoefficients k K L s t) X (upperFieldAlgHom k K L s t T i q)
  let (z : Σ i, Above k K L s t T i) :
      TopologicalSpace (RingPoints (upperCoefficients k K L s t) X (upperFactor k K L s t T z.1 z.2)) :=
    fieldValuedPointTopology (upperCoefficients k K L s t) X (upperFieldAlgHom k K L s t T z.1 z.2)
  let curryHomeomorph :
      (∀ i, ∀ q : Above k K L s t T i,
        RingPoints (upperCoefficients k K L s t) X (upperFactor k K L s t T i q)) ≃ₜ
      (∀ z : Σ i, Above k K L s t T i,
        RingPoints (upperCoefficients k K L s t) X (upperFactor k K L s t T z.1 z.2)) :=
    { toFun := fun x z => x z.1 z.2
      invFun := fun x i q => x ⟨i, q⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_pi fun z =>
        (continuous_apply z.2).comp (continuous_apply z.1)
      continuous_invFun := continuous_pi fun i => continuous_pi fun q =>
        continuous_apply (⟨i, q⟩ : Σ i, Above k K L s t T i) }
  exact ((AdelicSpaceStageCoordinates.curveStageHomeomorph k K (curvePlacePrincipalExceptional k K s (t : K)) T W hWsep hWft hS).trans
    (Homeomorph.piCongrRight fun i => factorPointHomeomorph k K L s t T X h hqs hft i)).trans
    curryHomeomorph

/-- Each stage component is the exact original local tensor Weil map
after coefficient change along the original enlarged-level projection. -/
@[simp]
theorem levelPointHomeomorph_component
    (x : RingPoints (lowerCoefficients k K s t)
      (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)
      (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T))
    (i : CurvePlaceLevelFactorIndex k K T.val) (q : Above k K L s t T i) :
    levelPointHomeomorph k K L s t T X h hqs hft hWsep hWft hS x ⟨i, q⟩ =
      completedTensorSpaceWeilRestrictionPointMap (lowerCoefficients k K s t) (upperCoefficients k K L s t)
        (CurvePlaceLevelFactor k K T.val i) (upperFactor k K L s t T i)
        (CurvePlacePrincipalSIntegerFixedLevelWeil.tensorEquiv k K L s t T i)
        (CurvePlacePrincipalSIntegerFixedLevelWeil.tensorEquiv_one_tmul k K L s t T i) X h
        (RingPoints.changeRing (CurvePlacePrincipalSIntegerFixedLevelWeil.levelFactorAlgHom k K s t T i) x) q := by
  change factorPointHomeomorph k K L s t T X h hqs hft i
    (AdelicSpaceStageCoordinates.curveStageHomeomorph k K (curvePlacePrincipalExceptional k K s (t : K)) T
      (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)
      hWsep hWft hS x i) q = _
  rw [factorPointHomeomorph_apply, AdelicSpaceStageCoordinates.curveStageHomeomorph_apply]
  rfl

end Langlands.Global.CurvePlacePrincipalSIntegerSpaceFixedLevelWeil
