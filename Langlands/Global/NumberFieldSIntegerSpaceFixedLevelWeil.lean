import Langlands.Global.NumberFieldSIntegerSpaceWeilTopology
import Langlands.Global.AdelicSpaceStageCoordinates
import Langlands.Global.NumberFieldSIntegerFixedLevelWeil

/-! # Fixed-model number-field stages and original local Weil factors -/

noncomputable section

universe u

open CategoryTheory Topology IsDedekindDomain
open _root_.AlgebraicGeometry
open scoped NumberField TensorProduct NumberField.LiesOver
  Langlands.Global Langlands.Global.NumberFieldSIntegers
  Langlands.Global.NumberFieldSIntegerLocalTensor
  Langlands.Global.NumberFieldSIntegerFieldTensor
  Langlands.Global.NumberFieldSIntegerLevelWeil
  Langlands.Global.NumberFieldSIntegerFixedLevelWeil
  Langlands.Global.FixedModelLocalProduct
  Langlands.Global.AdelicSpaceStageCoordinates
  Langlands.Global.AdelicFunctoriality.FiniteExtension
  Langlands.Global.AdelicFunctoriality.InfiniteExtension
  Langlands.Global.AdelicFunctoriality.IntegralTensor
  Langlands.Global.AdelicFunctoriality.IntegralTopology

namespace Langlands.Global.NumberFieldSIntegerSpaceFixedLevelWeil

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology
open AdelicFunctoriality NumberFieldSIntegerLevelWeil
open NumberFieldSIntegerSpaceWeilTopology (lowerCoefficients upperCoefficients)

set_option backward.isDefEq.respectTransparency false

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (S : Finset (FinitePlace K)) (T : AdelicLevelIndexAbove S)

/-- The original upper field containing an upper factor of the enlarged level. -/
def upperField (i : NumberFieldLevelFactorIndex K T.val) : Above K L T.val i → Type u :=
  match i with
  | .inl _ => fun q => q.1.Completion
  | .inr (.inl _) => fun q => q.1.adicCompletion L
  | .inr (.inr _) => fun q => q.1.adicCompletion L

scoped instance upperFieldField (i) (q : Above K L T.val i) :
    Field (upperField K L S T i q) := by
  cases i with
  | inl p => dsimp [upperField]; infer_instance
  | inr z => cases z <;> dsimp [upperField] <;> infer_instance

scoped instance upperFieldTopology (i) (q : Above K L T.val i) :
    TopologicalSpace (upperField K L S T i q) := by
  cases i with
  | inl p => dsimp [upperField]; infer_instance
  | inr z => cases z <;> dsimp [upperField] <;> infer_instance

scoped instance upperFieldCoefficientAlgebra (i) (q : Above K L T.val i) :
    Algebra (upperCoefficients K L S) (upperField K L S T i q) := by
  cases i with
  | inl p => exact inferInstanceAs (Algebra (upperCoefficients K L S) q.1.Completion)
  | inr z =>
    cases z <;> exact inferInstanceAs (Algebra (upperCoefficients K L S) (q.1.adicCompletion L))

/-- The original identity or valuation-ring inclusion on each upper coordinate. -/
def upperFieldAlgHom (i : NumberFieldLevelFactorIndex K T.val) (q : Above K L T.val i) :
    upperFactor K L T.val i q →ₐ[upperCoefficients K L S] upperField K L S T i q := by
  cases i with
  | inl p => exact AlgHom.id _ _
  | inr z =>
    cases z with
    | inl p => exact AlgHom.id _ _
    | inr p =>
      letI : Fact (p.1 ∉ S) := ⟨fun hp => p.2 (T.property hp)⟩
      exact Algebra.algHom (upperCoefficients K L S) (q.1.adicCompletionIntegers L)
        (q.1.adicCompletion L)

scoped instance lowerFieldNormed (i : NumberFieldLevelFactorIndex K T.val) :
    NontriviallyNormedField (NumberFieldLevelField K T.val i) := by
  cases i with
  | inl p => exact AdelicSpaceLocalFields.infiniteNormedField K p
  | inr z =>
    cases z <;> exact AdelicSpaceLocalFields.normedField (NumberField.RingOfIntegers K) K _

scoped instance upperFieldNormed (i) (q : Above K L T.val i) :
    NontriviallyNormedField (upperField K L S T i q) := by
  cases i with
  | inl p => exact AdelicSpaceLocalFields.infiniteNormedField L q.1
  | inr z =>
    cases z <;> exact AdelicSpaceLocalFields.normedField (NumberField.RingOfIntegers L) L q.1

scoped instance fieldFactorAlgebra (i) (q : Above K L T.val i) :
    Algebra (NumberFieldLevelField K T.val i) (upperField K L S T i q) := by
  cases i with
  | inl p => exact inferInstanceAs (Algebra p.Completion q.1.Completion)
  | inr z =>
    cases z <;> exact inferInstanceAs (Algebra ((_ : FinitePlace K).adicCompletion K) (q.1.adicCompletion L))

scoped instance fieldFactorContinuousSMul (i) (q : Above K L T.val i) :
    ContinuousSMul (NumberFieldLevelField K T.val i) (upperField K L S T i q) := by
  cases i with
  | inl p => exact inferInstanceAs (ContinuousSMul p.Completion q.1.Completion)
  | inr z =>
    cases z <;> exact inferInstanceAs (ContinuousSMul ((_ : FinitePlace K).adicCompletion K) (q.1.adicCompletion L))

scoped instance fieldFactorFinite (i) (q : Above K L T.val i) :
    FiniteDimensional (NumberFieldLevelField K T.val i) (upperField K L S T i q) := by
  cases i with
  | inl p => exact InfiniteExtension.local_finite p q.1
  | inr z => cases z <;> exact FiniteExtension.local_finite _ q.1

scoped instance lowerFieldComplete (i : NumberFieldLevelFactorIndex K T.val) :
    CompleteSpace (NumberFieldLevelField K T.val i) := by
  cases i with
  | inl p => change CompleteSpace p.Completion; infer_instance
  | inr z =>
    cases z with
    | inl p => change CompleteSpace (p.1.adicCompletion K); infer_instance
    | inr p => change CompleteSpace (p.1.adicCompletion K); infer_instance

scoped instance fieldFactorModuleTopology (i) (q : Above K L T.val i) :
    IsModuleTopology (NumberFieldLevelField K T.val i) (upperField K L S T i q) := by
  cases i with
  | inl p => exact isModuleTopologyOfFiniteDimensional
  | inr z => cases z <;> exact isModuleTopologyOfFiniteDimensional

/-- Henselianity for the original lower completed field at every coordinate. -/
theorem lowerField_henselian (i : NumberFieldLevelFactorIndex K T.val) :
    IsHenselianValuedField (NumberFieldLevelField K T.val i) := by
  cases i with
  | inl p => exact AdelicSpaceLocalFields.infinite_isHenselianValuedField K p
  | inr z =>
    cases z <;> exact AdelicSpaceLocalFields.isHenselianValuedField (NumberField.RingOfIntegers K) K _

omit [NumberField K] in
/-- Henselianity for every original upper completed field. -/
theorem upperField_henselian (i) (q : Above K L T.val i) :
    IsHenselianValuedField (upperField K L S T i q) := by
  cases i with
  | inl p => exact AdelicSpaceLocalFields.infinite_isHenselianValuedField L q.1
  | inr z =>
    cases z <;> exact AdelicSpaceLocalFields.isHenselianValuedField (NumberField.RingOfIntegers L) L q.1

/-- The field tensor decomposition retaining the fixed-base action on the
original completed field. -/
def fieldTensorData (i : NumberFieldLevelFactorIndex K T.val) :
    { e : NumberFieldLevelField K T.val i ⊗[lowerCoefficients K S]
        upperCoefficients K L S ≃ₐ[NumberFieldLevelField K T.val i]
        (∀ q : Above K L T.val i, upperField K L S T i q) //
      ∀ (b : upperCoefficients K L S) (q : Above K L T.val i),
        e (1 ⊗ₜ[lowerCoefficients K S] b) q =
          algebraMap (upperCoefficients K L S) (upperField K L S T i q) b } := by
  cases i with
  | inl p =>
    have hF : AdelicSpaceStageCoordinates.numberFieldFieldAlgebra K S T (.inl p) =
        Subalgebra.toAlgebra (α := p.Completion) (lowerCoefficients K S) :=
      Algebra.algebra_ext _ _ fun _ => rfl
    rw [hF]
    exact ⟨NumberFieldSIntegerInfiniteTensor.tensorEquiv K L S p,
      NumberFieldSIntegerInfiniteTensor.tensorEquiv_one_tmul K L S p⟩
  | inr z =>
    cases z with
    | inl p =>
      have hF : AdelicSpaceStageCoordinates.numberFieldFieldAlgebra K S T (.inr (.inl p)) =
          Subalgebra.toAlgebra (α := p.1.adicCompletion K) (lowerCoefficients K S) :=
        Algebra.algebra_ext _ _ fun _ => rfl
      rw [hF]
      exact ⟨NumberFieldSIntegerFieldTensor.tensorEquiv K L S p.1,
        NumberFieldSIntegerFieldTensor.tensorEquiv_one_tmul K L S p.1⟩
    | inr p =>
      have hF : AdelicSpaceStageCoordinates.numberFieldFieldAlgebra K S T (.inr (.inr p)) =
          Subalgebra.toAlgebra (α := p.1.adicCompletion K) (lowerCoefficients K S) :=
        Algebra.algebra_ext _ _ fun _ => rfl
      rw [hF]
      exact ⟨NumberFieldSIntegerFieldTensor.tensorEquiv K L S p.1,
        NumberFieldSIntegerFieldTensor.tensorEquiv_one_tmul K L S p.1⟩

variable
  (X : AlgebraicSpace (Spec (CommRingCat.of (upperCoefficients K L S))))
  (h : IsAlgebraicSpace _
    ((ringWeilRestriction (lowerCoefficients K S) (upperCoefficients K L S)).obj X.toSheaf))
  (hqs : IsQuasiSeparated X) (hft : FiniteTypeOverRing (upperCoefficients K L S) X)

include hqs hft in
/-- The field comparison at each coordinate uses the original completed
fields, with their fixed-base coefficient actions. -/
theorem fieldPointMap_isHomeomorph (i : NumberFieldLevelFactorIndex K T.val) :
    @IsHomeomorph _ _
      (fieldValuedPointTopology (lowerCoefficients K S)
        (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
        (AlgHom.id _ (NumberFieldLevelField K T.val i)))
      (coordinateProductTopology (upperCoefficients K L S) X
        (upperField K L S T i) (upperField K L S T i) (fun _ => AlgHom.id _ _))
      (completedTensorSpaceWeilRestrictionPointMap
        (lowerCoefficients K S) (upperCoefficients K L S) (NumberFieldLevelField K T.val i)
        (upperField K L S T i) (fieldTensorData K L S T i).1 (fieldTensorData K L S T i).2 X h) := by
  cases i with
  | inl p =>
    exact WeilRestrictionTensorTopology.isHomeomorph_completedTensorSpaceWeilRestrictionPointMap_finiteType
      (lowerCoefficients K S) (upperCoefficients K L S) (NumberFieldLevelField K T.val (.inl p))
      (upperField K L S T (.inl p)) (fieldTensorData K L S T (.inl p)).1 (fieldTensorData K L S T (.inl p)).2
      X h hqs hft (lowerField_henselian K S T (.inl p)) (upperField_henselian K L S T (.inl p))
  | inr z =>
    cases z with
    | inl p =>
      exact WeilRestrictionTensorTopology.isHomeomorph_completedTensorSpaceWeilRestrictionPointMap_finiteType
        (lowerCoefficients K S) (upperCoefficients K L S) (NumberFieldLevelField K T.val (.inr (.inl p)))
        (upperField K L S T (.inr (.inl p))) (fieldTensorData K L S T (.inr (.inl p))).1 (fieldTensorData K L S T (.inr (.inl p))).2
        X h hqs hft (lowerField_henselian K S T (.inr (.inl p))) (upperField_henselian K L S T (.inr (.inl p)))
    | inr p =>
      exact WeilRestrictionTensorTopology.isHomeomorph_completedTensorSpaceWeilRestrictionPointMap_finiteType
        (lowerCoefficients K S) (upperCoefficients K L S) (NumberFieldLevelField K T.val (.inr (.inr p)))
        (upperField K L S T (.inr (.inr p))) (fieldTensorData K L S T (.inr (.inr p))).1 (fieldTensorData K L S T (.inr (.inr p))).2
        X h hqs hft (lowerField_henselian K S T (.inr (.inr p))) (upperField_henselian K L S T (.inr (.inr p)))

/-- At each enlarged-level coordinate the original Weil point topology
is the product of the original upper local factor topologies. -/
def factorPointHomeomorph (i : NumberFieldLevelFactorIndex K T.val) :
    letI : TopologicalSpace
        (RingPoints (lowerCoefficients K S)
          (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
          (NumberFieldLevelFactor K T.val i)) :=
      fieldValuedPointTopology (lowerCoefficients K S) _
        ((numberFieldLevelFieldAlgHom K T.val i).restrictScalars _)
    letI : ∀ q : Above K L T.val i, TopologicalSpace
        (RingPoints (upperCoefficients K L S) X (upperFactor K L T.val i q)) :=
      fun q => fieldValuedPointTopology (upperCoefficients K L S) X
        (upperFieldAlgHom K L S T i q)
    RingPoints (lowerCoefficients K S)
        (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
        (NumberFieldLevelFactor K T.val i) ≃ₜ
      (∀ q : Above K L T.val i,
        RingPoints (upperCoefficients K L S) X (upperFactor K L T.val i q)) := by
  letI : Algebra (lowerCoefficients K S) (NumberFieldLevelField K T.val i) :=
    AdelicSpaceStageCoordinates.numberFieldFieldAlgebra K S T i
  have hfg : ∀ (c : NumberFieldLevelFactor K T.val i) (q : Above K L T.val i),
      upperFieldAlgHom K L S T i q
          (algebraMap (NumberFieldLevelFactor K T.val i) (upperFactor K L T.val i q) c) =
        algebraMap (NumberFieldLevelField K T.val i) (upperField K L S T i q)
          (((numberFieldLevelFieldAlgHom K T.val i).restrictScalars (lowerCoefficients K S)) c) := by
    intro c q
    cases i with
    | inl p => rfl
    | inr z => cases z <;> rfl
  have hfield := fieldPointMap_isHomeomorph K L S T X h hqs hft i
  exact WeilRestrictionTensorTopology.integralPointHomeomorph
    (lowerCoefficients K S) (upperCoefficients K L S)
    (NumberFieldLevelFactor K T.val i) (NumberFieldLevelField K T.val i)
    (upperFactor K L T.val i) (upperField K L S T i)
    (NumberFieldSIntegerFixedLevelWeil.tensorEquiv K L S T i)
    (NumberFieldSIntegerFixedLevelWeil.tensorEquiv_one_tmul K L S T i)
    (fieldTensorData K L S T i).1 (fieldTensorData K L S T i).2
    ((numberFieldLevelFieldAlgHom K T.val i).restrictScalars _)
    (upperFieldAlgHom K L S T i) hfg X h hfield

@[simp]
theorem factorPointHomeomorph_apply (i : NumberFieldLevelFactorIndex K T.val)
    (x : RingPoints (lowerCoefficients K S)
      (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
      (NumberFieldLevelFactor K T.val i)) (q : Above K L T.val i) :
    factorPointHomeomorph K L S T X h hqs hft i x q =
      completedTensorSpaceWeilRestrictionPointMap (lowerCoefficients K S) (upperCoefficients K L S)
        (NumberFieldLevelFactor K T.val i) (upperFactor K L T.val i)
        (NumberFieldSIntegerFixedLevelWeil.tensorEquiv K L S T i)
        (NumberFieldSIntegerFixedLevelWeil.tensorEquiv_one_tmul K L S T i) X h x q := by
  simp only [factorPointHomeomorph, WeilRestrictionTensorTopology.integralPointHomeomorph_apply]

variable
  (hWsep : IsSeparated
    (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h))
  (hWft : FiniteTypeOverRing (lowerCoefficients K S)
    (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h))

/-- Every stage of the fixed original Weil model has the product topology
of its original upper local factors, including all infinite places. -/
def levelPointHomeomorph :
    letI := numberFieldSpaceStageTopology K S
      (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h) T
    letI : ∀ z : Σ i, Above K L T.val i, TopologicalSpace
        (RingPoints (upperCoefficients K L S) X (upperFactor K L T.val z.1 z.2)) :=
      fun z => fieldValuedPointTopology (upperCoefficients K L S) X
        (upperFieldAlgHom K L S T z.1 z.2)
    RingPoints (lowerCoefficients K S)
        (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
        (numberFieldAdeleLevelOver K S T) ≃ₜ
      (∀ z : Σ i, Above K L T.val i,
        RingPoints (upperCoefficients K L S) X (upperFactor K L T.val z.1 z.2)) := by
  let W := ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h
  let : TopologicalSpace (RingPoints (lowerCoefficients K S) W (numberFieldAdeleLevelOver K S T)) :=
    numberFieldSpaceStageTopology K S W T
  let (i : NumberFieldLevelFactorIndex K T.val) :
      TopologicalSpace (RingPoints (lowerCoefficients K S) W (NumberFieldLevelFactor K T.val i)) :=
    fieldValuedPointTopology (lowerCoefficients K S) W
      ((numberFieldLevelFieldAlgHom K T.val i).restrictScalars _)
  let (i : NumberFieldLevelFactorIndex K T.val) (q : Above K L T.val i) :
      TopologicalSpace (RingPoints (upperCoefficients K L S) X (upperFactor K L T.val i q)) :=
    fieldValuedPointTopology (upperCoefficients K L S) X (upperFieldAlgHom K L S T i q)
  let (z : Σ i, Above K L T.val i) :
      TopologicalSpace (RingPoints (upperCoefficients K L S) X (upperFactor K L T.val z.1 z.2)) :=
    fieldValuedPointTopology (upperCoefficients K L S) X (upperFieldAlgHom K L S T z.1 z.2)
  let curryHomeomorph :
      (∀ i, ∀ q : Above K L T.val i,
        RingPoints (upperCoefficients K L S) X (upperFactor K L T.val i q)) ≃ₜ
      (∀ z : Σ i, Above K L T.val i,
        RingPoints (upperCoefficients K L S) X (upperFactor K L T.val z.1 z.2)) :=
    { toFun := fun x z => x z.1 z.2
      invFun := fun x i q => x ⟨i, q⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_pi fun z =>
        (continuous_apply z.2).comp (continuous_apply z.1)
      continuous_invFun := continuous_pi fun i => continuous_pi fun q =>
        continuous_apply (⟨i, q⟩ : Σ i, Above K L T.val i) }
  exact ((AdelicSpaceStageCoordinates.numberFieldStageHomeomorph K S T W hWsep hWft).trans
    (Homeomorph.piCongrRight fun i => factorPointHomeomorph K L S T X h hqs hft i)).trans
    curryHomeomorph

/-- Each stage component is the exact original local tensor Weil map
after coefficient change along the original enlarged-level projection. -/
@[simp]
theorem levelPointHomeomorph_component
    (x : RingPoints (lowerCoefficients K S)
      (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
      (numberFieldAdeleLevelOver K S T))
    (i : NumberFieldLevelFactorIndex K T.val) (q : Above K L T.val i) :
    levelPointHomeomorph K L S T X h hqs hft hWsep hWft x ⟨i, q⟩ =
      completedTensorSpaceWeilRestrictionPointMap (lowerCoefficients K S) (upperCoefficients K L S)
        (NumberFieldLevelFactor K T.val i) (upperFactor K L T.val i)
        (NumberFieldSIntegerFixedLevelWeil.tensorEquiv K L S T i)
        (NumberFieldSIntegerFixedLevelWeil.tensorEquiv_one_tmul K L S T i) X h
        (RingPoints.changeRing (NumberFieldSIntegerFixedLevelWeil.levelFactorAlgHom K S T i) x) q := by
  change factorPointHomeomorph K L S T X h hqs hft i
    (AdelicSpaceStageCoordinates.numberFieldStageHomeomorph K S T
      (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
      hWsep hWft x i) q = _
  rw [factorPointHomeomorph_apply, AdelicSpaceStageCoordinates.numberFieldStageHomeomorph_apply]
  rfl

end Langlands.Global.NumberFieldSIntegerSpaceFixedLevelWeil
