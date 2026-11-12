import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionTensorFiniteTypeTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionTensorIntegralTopology
import Langlands.Global.NumberFieldSIntegerLevelWeil
import Langlands.Global.AdelicSpaceLocalFields

/-! # Original number-field local coordinates of a space Weil restriction -/

noncomputable section

universe u

open CategoryTheory Topology IsDedekindDomain
open _root_.AlgebraicGeometry
open scoped NumberField TensorProduct NumberField.LiesOver
  Langlands.Global Langlands.Global.NumberFieldSIntegers
  Langlands.Global.NumberFieldSIntegerLocalTensor
  Langlands.Global.NumberFieldSIntegerFieldTensor
  Langlands.Global.AdelicFunctoriality.FiniteExtension
  Langlands.Global.AdelicFunctoriality.InfiniteExtension
  Langlands.Global.AdelicFunctoriality.IntegralTensor
  Langlands.Global.AdelicFunctoriality.IntegralTopology

namespace Langlands.Global.NumberFieldSIntegerSpaceWeilTopology

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology
open AdelicFunctoriality

set_option backward.isDefEq.respectTransparency false

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (S : Finset (FinitePlace K))

/-- The original lower ring of S-integers. -/
abbrev lowerCoefficients := ((S : Set (FinitePlace K)).integer K)

/-- The original upper S-integer ring for the full preimage of S. -/
abbrev upperCoefficients :=
  (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) :
    Set (FinitePlace L)).integer L)

variable
  (X : AlgebraicSpace (Spec (CommRingCat.of (upperCoefficients K L S))))
  (h : IsAlgebraicSpace _
    ((ringWeilRestriction (lowerCoefficients K S) (upperCoefficients K L S)).obj X.toSheaf))
  (hqs : IsQuasiSeparated X) (hft : FiniteTypeOverRing (upperCoefficients K L S) X)

section FinitePlace

variable (v : FinitePlace K)

local instance lowerNormedField : NontriviallyNormedField (v.adicCompletion K) :=
  AdelicSpaceLocalFields.normedField (NumberField.RingOfIntegers K) K v

local instance upperNormedField (q : FinitePlacesAbove L v) :
    NontriviallyNormedField (q.1.adicCompletion L) :=
  AdelicSpaceLocalFields.normedField (NumberField.RingOfIntegers L) L q.1

local instance upperFinite (q : FinitePlacesAbove L v) :
    FiniteDimensional (v.adicCompletion K) (q.1.adicCompletion L) :=
  FiniteExtension.local_finite v q.1

local instance upperModuleTopology (q : FinitePlacesAbove L v) :
    IsModuleTopology (v.adicCompletion K) (q.1.adicCompletion L) :=
  isModuleTopologyOfFiniteDimensional

/-- The original finite-field tensor factor map is a homeomorphism,
with the actual independently normalized completion topologies. -/
def fieldPointHomeomorph :
    letI : TopologicalSpace
        (RingPoints (lowerCoefficients K S)
          (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
          (v.adicCompletion K)) :=
      fieldValuedPointTopology (lowerCoefficients K S) _ (AlgHom.id _ _)
    letI : ∀ q : FinitePlacesAbove L v,
        TopologicalSpace (RingPoints (upperCoefficients K L S) X (q.1.adicCompletion L)) :=
      fun q => fieldValuedPointTopology (upperCoefficients K L S) X
        (AlgHom.id _ (q.1.adicCompletion L))
    RingPoints (lowerCoefficients K S)
        (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
        (v.adicCompletion K) ≃ₜ
      (∀ q : FinitePlacesAbove L v,
        RingPoints (upperCoefficients K L S) X (q.1.adicCompletion L)) :=
  WeilRestrictionTensorTopology.finiteTypeTensorPointHomeomorph
    (lowerCoefficients K S) (upperCoefficients K L S) (v.adicCompletion K)
    (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)
    (NumberFieldSIntegerFieldTensor.tensorEquiv K L S v)
    (NumberFieldSIntegerFieldTensor.tensorEquiv_one_tmul K L S v) X h hqs hft
    (AdelicSpaceLocalFields.isHenselianValuedField (NumberField.RingOfIntegers K) K v)
    (fun q => AdelicSpaceLocalFields.isHenselianValuedField
      (NumberField.RingOfIntegers L) L q.1)

@[simp]
theorem fieldPointHomeomorph_apply
    (x : RingPoints (lowerCoefficients K S)
      (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
      (v.adicCompletion K)) (q : FinitePlacesAbove L v) :
    fieldPointHomeomorph K L S X h hqs hft v x q =
      completedTensorSpaceWeilRestrictionPointMap
        (lowerCoefficients K S) (upperCoefficients K L S) (v.adicCompletion K)
        (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)
        (NumberFieldSIntegerFieldTensor.tensorEquiv K L S v)
        (NumberFieldSIntegerFieldTensor.tensorEquiv_one_tmul K L S v) X h x q := by
  simp only [fieldPointHomeomorph,
    WeilRestrictionTensorTopology.finiteTypeTensorPointHomeomorph_apply]

include hqs hft in
/-- The field comparison property for the exact original tensor factor map. -/
theorem isHomeomorph_fieldPointMap :
    @IsHomeomorph _ _
      (fieldValuedPointTopology (lowerCoefficients K S)
        (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
        (AlgHom.id _ (v.adicCompletion K)))
      (coordinateProductTopology (upperCoefficients K L S) X
        (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)
        (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)
        (fun _ => AlgHom.id _ _))
      (completedTensorSpaceWeilRestrictionPointMap
        (lowerCoefficients K S) (upperCoefficients K L S) (v.adicCompletion K)
        (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)
        (NumberFieldSIntegerFieldTensor.tensorEquiv K L S v)
        (NumberFieldSIntegerFieldTensor.tensorEquiv_one_tmul K L S v) X h) :=
  WeilRestrictionTensorTopology.isHomeomorph_completedTensorSpaceWeilRestrictionPointMap_finiteType
    (lowerCoefficients K S) (upperCoefficients K L S) (v.adicCompletion K)
    (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)
    (NumberFieldSIntegerFieldTensor.tensorEquiv K L S v)
    (NumberFieldSIntegerFieldTensor.tensorEquiv_one_tmul K L S v) X h hqs hft
    (AdelicSpaceLocalFields.isHenselianValuedField (NumberField.RingOfIntegers K) K v)
    (fun q => AdelicSpaceLocalFields.isHenselianValuedField
      (NumberField.RingOfIntegers L) L q.1)

variable [Fact (v ∉ S)]

/-- At a place outside S, the original integral tensor factor map is
a homeomorphism for the topologies induced from the original fields. -/
def integralPointHomeomorph :
    letI : TopologicalSpace
        (RingPoints (lowerCoefficients K S)
          (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
          (v.adicCompletionIntegers K)) :=
      fieldValuedPointTopology (lowerCoefficients K S) _
        (Algebra.algHom (lowerCoefficients K S) (v.adicCompletionIntegers K)
          (v.adicCompletion K))
    letI : ∀ q : FinitePlacesAbove L v, TopologicalSpace
        (RingPoints (upperCoefficients K L S) X (q.1.adicCompletionIntegers L)) :=
      fun q => fieldValuedPointTopology (upperCoefficients K L S) X
        (Algebra.algHom (upperCoefficients K L S) (q.1.adicCompletionIntegers L)
          (q.1.adicCompletion L))
    RingPoints (lowerCoefficients K S)
        (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
        (v.adicCompletionIntegers K) ≃ₜ
      (∀ q : FinitePlacesAbove L v,
        RingPoints (upperCoefficients K L S) X (q.1.adicCompletionIntegers L)) :=
  WeilRestrictionTensorTopology.integralPointHomeomorph
    (lowerCoefficients K S) (upperCoefficients K L S)
    (v.adicCompletionIntegers K) (v.adicCompletion K)
    (fun q : FinitePlacesAbove L v => q.1.adicCompletionIntegers L)
    (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)
    (NumberFieldSIntegerLocalTensor.completedTensorEquiv K S v L)
    (NumberFieldSIntegerLocalTensor.completedTensorEquiv_one_tmul K S v L)
    (NumberFieldSIntegerFieldTensor.tensorEquiv K L S v)
    (NumberFieldSIntegerFieldTensor.tensorEquiv_one_tmul K L S v)
    (Algebra.algHom (lowerCoefficients K S) (v.adicCompletionIntegers K)
      (v.adicCompletion K))
    (fun q => Algebra.algHom (upperCoefficients K L S) (q.1.adicCompletionIntegers L)
      (q.1.adicCompletion L))
    (fun _ _ => rfl) X h (isHomeomorph_fieldPointMap K L S X h hqs hft v)

@[simp]
theorem integralPointHomeomorph_apply
    (x : RingPoints (lowerCoefficients K S)
      (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
      (v.adicCompletionIntegers K)) (q : FinitePlacesAbove L v) :
    integralPointHomeomorph K L S X h hqs hft v x q =
      completedTensorSpaceWeilRestrictionPointMap
        (lowerCoefficients K S) (upperCoefficients K L S) (v.adicCompletionIntegers K)
        (fun q : FinitePlacesAbove L v => q.1.adicCompletionIntegers L)
        (NumberFieldSIntegerLocalTensor.completedTensorEquiv K S v L)
        (NumberFieldSIntegerLocalTensor.completedTensorEquiv_one_tmul K S v L) X h x q := by
  simp only [integralPointHomeomorph, WeilRestrictionTensorTopology.integralPointHomeomorph_apply]

end FinitePlace

section InfinitePlace

variable (v : NumberField.InfinitePlace K)

local instance lowerInfiniteNormedField : NontriviallyNormedField v.Completion :=
  AdelicSpaceLocalFields.infiniteNormedField K v

local instance upperInfiniteNormedField (q : InfinitePlacesAbove L v) :
    NontriviallyNormedField q.1.Completion :=
  AdelicSpaceLocalFields.infiniteNormedField L q.1

local instance upperInfiniteModuleTopology (q : InfinitePlacesAbove L v) :
    IsModuleTopology v.Completion q.1.Completion :=
  isModuleTopologyOfFiniteDimensional

/-- The original infinite-place tensor comparison, including real and
complex factors, with the original field-valued point topologies. -/
def infinitePointHomeomorph :
    letI : TopologicalSpace
        (RingPoints (lowerCoefficients K S)
          (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
          v.Completion) :=
      fieldValuedPointTopology (lowerCoefficients K S) _ (AlgHom.id _ _)
    letI : ∀ q : InfinitePlacesAbove L v, TopologicalSpace
        (RingPoints (upperCoefficients K L S) X q.1.Completion) :=
      fun q => fieldValuedPointTopology (upperCoefficients K L S) X
        (AlgHom.id _ q.1.Completion)
    RingPoints (lowerCoefficients K S)
        (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
        v.Completion ≃ₜ
      (∀ q : InfinitePlacesAbove L v, RingPoints (upperCoefficients K L S) X q.1.Completion) :=
  WeilRestrictionTensorTopology.finiteTypeTensorPointHomeomorph
    (lowerCoefficients K S) (upperCoefficients K L S) v.Completion
    (fun q : InfinitePlacesAbove L v => q.1.Completion)
    (NumberFieldSIntegerInfiniteTensor.tensorEquiv K L S v)
    (NumberFieldSIntegerInfiniteTensor.tensorEquiv_one_tmul K L S v) X h hqs hft
    (AdelicSpaceLocalFields.infinite_isHenselianValuedField K v)
    (fun q => AdelicSpaceLocalFields.infinite_isHenselianValuedField L q.1)

@[simp]
theorem infinitePointHomeomorph_apply
    (x : RingPoints (lowerCoefficients K S)
      (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
      v.Completion) (q : InfinitePlacesAbove L v) :
    infinitePointHomeomorph K L S X h hqs hft v x q =
      completedTensorSpaceWeilRestrictionPointMap
        (lowerCoefficients K S) (upperCoefficients K L S) v.Completion
        (fun q : InfinitePlacesAbove L v => q.1.Completion)
        (NumberFieldSIntegerInfiniteTensor.tensorEquiv K L S v)
        (NumberFieldSIntegerInfiniteTensor.tensorEquiv_one_tmul K L S v) X h x q := by
  simp only [infinitePointHomeomorph,
    WeilRestrictionTensorTopology.finiteTypeTensorPointHomeomorph_apply]

end InfinitePlace

end Langlands.Global.NumberFieldSIntegerSpaceWeilTopology
