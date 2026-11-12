import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionTensorFiniteTypeTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionTensorIntegralTopology
import Langlands.Global.CurvePlacePrincipalSIntegerLevelWeil
import Langlands.Global.AdelicSpaceLocalFields

/-! # Original curve-place local coordinates of a space Weil restriction -/

noncomputable section

universe u

open CategoryTheory Topology IsDedekindDomain IntermediateField AlgebraicCurve
open _root_.AlgebraicGeometry
open scoped TensorProduct AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global Langlands.Global.CurvePlacePrincipalSIntegers
  Langlands.Global.CurvePlacePrincipalSIntegerLocalTensor
  Langlands.Global.CurvePlacePrincipalSIntegerFieldTensor
  Langlands.Global.CurvePlaceCompletionExtension
  Langlands.Global.CurvePlaceCompletedIntegersExtension
  Langlands.Global.CurvePlaceIntegralClosure Langlands.Global.CurvePlaceIntegralTensor
  Langlands.Global.CurvePlaceIntegralTopology

namespace Langlands.Global.CurvePlacePrincipalSIntegerSpaceWeilTopology

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L] (s : K) [FiniteDimensional k⟮s⟯ K]
  (t : CurveModel.chartRing k ({s} : Set K)) [Fact (t ≠ 0)]

/-- The original lower principal ring of S-integers. -/
abbrev lowerCoefficients :=
  curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))

/-- The original upper S-integer ring for the full exceptional preimage. -/
abbrev upperCoefficients :=
  curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
    (curvePlacePrincipalExceptional k K s (t : K)))

variable
  (X : AlgebraicSpace (Spec (CommRingCat.of (upperCoefficients k K L s t))))
  (h : IsAlgebraicSpace _
    ((ringWeilRestriction (lowerCoefficients k K s t) (upperCoefficients k K L s t)).obj X.toSheaf))
  (hqs : IsQuasiSeparated X) (hft : FiniteTypeOverRing (upperCoefficients k K L s t) X)

section LocalPlace

variable (v : Place k K)

local instance lowerNormedField : NontriviallyNormedField (curvePlaceCompletion v) :=
  AdelicSpaceLocalFields.normedField v.toValuationSubring K v.heightOneSpectrum

local instance upperNormedField (q : CurvePlacesAbove k L v) :
    NontriviallyNormedField (curvePlaceCompletion q.1) :=
  AdelicSpaceLocalFields.normedField q.1.toValuationSubring L q.1.heightOneSpectrum

local instance upperFinite (q : CurvePlacesAbove k L v) :
    FiniteDimensional (curvePlaceCompletion v) (curvePlaceCompletion q.1) :=
  CurvePlaceCompletionExtension.localFinite v q

local instance upperModuleTopology (q : CurvePlacesAbove k L v) :
    IsModuleTopology (curvePlaceCompletion v) (curvePlaceCompletion q.1) :=
  isModuleTopologyOfFiniteDimensional

/-- The original curve-place field tensor factor map is a homeomorphism,
with the actual independently normalized completion topologies. -/
def fieldPointHomeomorph :
    letI : TopologicalSpace
        (RingPoints (lowerCoefficients k K s t)
          (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)
          (curvePlaceCompletion v)) :=
      fieldValuedPointTopology (lowerCoefficients k K s t) _ (AlgHom.id _ _)
    letI : ∀ q : CurvePlacesAbove k L v,
        TopologicalSpace (RingPoints (upperCoefficients k K L s t) X (curvePlaceCompletion q.1)) :=
      fun q => fieldValuedPointTopology (upperCoefficients k K L s t) X
        (AlgHom.id _ (curvePlaceCompletion q.1))
    RingPoints (lowerCoefficients k K s t)
        (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)
        (curvePlaceCompletion v) ≃ₜ
      (∀ q : CurvePlacesAbove k L v,
        RingPoints (upperCoefficients k K L s t) X (curvePlaceCompletion q.1)) :=
  WeilRestrictionTensorTopology.finiteTypeTensorPointHomeomorph
    (lowerCoefficients k K s t) (upperCoefficients k K L s t) (curvePlaceCompletion v)
    (fun q : CurvePlacesAbove k L v => curvePlaceCompletion q.1)
    (CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv k K L s t v)
    (CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv_one_tmul k K L s t v) X h hqs hft
    (AdelicSpaceLocalFields.isHenselianValuedField v.toValuationSubring K v.heightOneSpectrum)
    (fun q => AdelicSpaceLocalFields.isHenselianValuedField
      q.1.toValuationSubring L q.1.heightOneSpectrum)

@[simp]
theorem fieldPointHomeomorph_apply
    (x : RingPoints (lowerCoefficients k K s t)
      (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)
      (curvePlaceCompletion v)) (q : CurvePlacesAbove k L v) :
    fieldPointHomeomorph k K L s t X h hqs hft v x q =
      completedTensorSpaceWeilRestrictionPointMap
        (lowerCoefficients k K s t) (upperCoefficients k K L s t) (curvePlaceCompletion v)
        (fun q : CurvePlacesAbove k L v => curvePlaceCompletion q.1)
        (CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv k K L s t v)
        (CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv_one_tmul k K L s t v) X h x q := by
  simp only [fieldPointHomeomorph,
    WeilRestrictionTensorTopology.finiteTypeTensorPointHomeomorph_apply]

include hqs hft in
/-- The field comparison property for the exact original tensor factor map. -/
theorem isHomeomorph_fieldPointMap :
    @IsHomeomorph _ _
      (fieldValuedPointTopology (lowerCoefficients k K s t)
        (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)
        (AlgHom.id _ (curvePlaceCompletion v)))
      (coordinateProductTopology (upperCoefficients k K L s t) X
        (fun q : CurvePlacesAbove k L v => curvePlaceCompletion q.1)
        (fun q : CurvePlacesAbove k L v => curvePlaceCompletion q.1)
        (fun _ => AlgHom.id _ _))
      (completedTensorSpaceWeilRestrictionPointMap
        (lowerCoefficients k K s t) (upperCoefficients k K L s t) (curvePlaceCompletion v)
        (fun q : CurvePlacesAbove k L v => curvePlaceCompletion q.1)
        (CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv k K L s t v)
        (CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv_one_tmul k K L s t v) X h) :=
  WeilRestrictionTensorTopology.isHomeomorph_completedTensorSpaceWeilRestrictionPointMap_finiteType
    (lowerCoefficients k K s t) (upperCoefficients k K L s t) (curvePlaceCompletion v)
    (fun q : CurvePlacesAbove k L v => curvePlaceCompletion q.1)
    (CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv k K L s t v)
    (CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv_one_tmul k K L s t v) X h hqs hft
    (AdelicSpaceLocalFields.isHenselianValuedField v.toValuationSubring K v.heightOneSpectrum)
    (fun q => AdelicSpaceLocalFields.isHenselianValuedField
      q.1.toValuationSubring L q.1.heightOneSpectrum)

variable [Fact (v ∉ curvePlacePrincipalExceptional k K s (t : K))]

/-- At a place outside the principal exceptional set, the original integral tensor factor map is
a homeomorphism for the topologies induced from the original fields. -/
def integralPointHomeomorph :
    letI : TopologicalSpace
        (RingPoints (lowerCoefficients k K s t)
          (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)
          (curvePlaceCompletionIntegers v)) :=
      fieldValuedPointTopology (lowerCoefficients k K s t) _
        (Algebra.algHom (lowerCoefficients k K s t) (curvePlaceCompletionIntegers v)
          (curvePlaceCompletion v))
    letI : ∀ q : CurvePlacesAbove k L v, TopologicalSpace
        (RingPoints (upperCoefficients k K L s t) X (curvePlaceCompletionIntegers q.1)) :=
      fun q => fieldValuedPointTopology (upperCoefficients k K L s t) X
        (Algebra.algHom (upperCoefficients k K L s t) (curvePlaceCompletionIntegers q.1)
          (curvePlaceCompletion q.1))
    RingPoints (lowerCoefficients k K s t)
        (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)
        (curvePlaceCompletionIntegers v) ≃ₜ
      (∀ q : CurvePlacesAbove k L v,
        RingPoints (upperCoefficients k K L s t) X (curvePlaceCompletionIntegers q.1)) :=
  WeilRestrictionTensorTopology.integralPointHomeomorph
    (lowerCoefficients k K s t) (upperCoefficients k K L s t)
    (curvePlaceCompletionIntegers v) (curvePlaceCompletion v)
    (fun q : CurvePlacesAbove k L v => curvePlaceCompletionIntegers q.1)
    (fun q : CurvePlacesAbove k L v => curvePlaceCompletion q.1)
    (CurvePlacePrincipalSIntegerLocalTensor.completedTensorEquiv k K s t v L)
    (CurvePlacePrincipalSIntegerLocalTensor.completedTensorEquiv_one_tmul k K s t v L)
    (CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv k K L s t v)
    (CurvePlacePrincipalSIntegerFieldTensor.tensorEquiv_one_tmul k K L s t v)
    (Algebra.algHom (lowerCoefficients k K s t) (curvePlaceCompletionIntegers v)
      (curvePlaceCompletion v))
    (fun q => Algebra.algHom (upperCoefficients k K L s t) (curvePlaceCompletionIntegers q.1)
      (curvePlaceCompletion q.1))
    (fun _ _ => rfl) X h (isHomeomorph_fieldPointMap k K L s t X h hqs hft v)

@[simp]
theorem integralPointHomeomorph_apply
    (x : RingPoints (lowerCoefficients k K s t)
      (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)
      (curvePlaceCompletionIntegers v)) (q : CurvePlacesAbove k L v) :
    integralPointHomeomorph k K L s t X h hqs hft v x q =
      completedTensorSpaceWeilRestrictionPointMap
        (lowerCoefficients k K s t) (upperCoefficients k K L s t) (curvePlaceCompletionIntegers v)
        (fun q : CurvePlacesAbove k L v => curvePlaceCompletionIntegers q.1)
        (CurvePlacePrincipalSIntegerLocalTensor.completedTensorEquiv k K s t v L)
        (CurvePlacePrincipalSIntegerLocalTensor.completedTensorEquiv_one_tmul k K s t v L) X h x q := by
  simp only [integralPointHomeomorph, WeilRestrictionTensorTopology.integralPointHomeomorph_apply]

end LocalPlace

end Langlands.Global.CurvePlacePrincipalSIntegerSpaceWeilTopology
