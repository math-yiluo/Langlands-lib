import Langlands.Representation.Smooth.FiniteLengthGrothendieckBilinear
import Langlands.Representation.Derivative.ProductDerivativesFiniteLength
import Mathlib.Algebra.DirectSum.Module

/-!
# The actual graded Grothendieck carrier and induction multiplication

The homogeneous groups are the published exact K0 groups of actual finite-length
smooth representations. The multiplication descends the actual binary normalized
product, including rank zero. Its separate exactness and its remaining ring laws
are explicit proposition targets, not implicit representation-theoretic axioms.
-/

noncomputable section

open CategoryTheory
open scoped DirectSum TensorProduct

namespace Langlands.Aubert

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual exact-K0 carrier in every natural rank, including rank zero. -/
abbrev GradedGrothendieckGroup :=
  letI := T.topology
  ⨁ n : ℕ, GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier

/-- The canonical homogeneous inclusion into the graded carrier. -/
def gradedInclusion (n : ℕ) :
    letI := T.topology
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
      GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  DirectSum.lof ℤ ℕ (fun k => GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} k F.Carrier) n

/-- Existing all-ranks finite-length preservation of the actual binary product. -/
theorem binaryProduct_preservesFiniteLength (a b : ℕ) :
    letI := T.topology
    SmoothRep.PreservesFiniteLength₂
      (T.binaryNormalizedProductFunctor.{uF, max uF uV} a b) := by
  let := T.topology
  intro A B hA hB
  exact Derivative.ProductDerivativesFiniteLength.binaryProduct_hasFiniteLength T
    (A, B) hA hB

/-- The exactness still needed to descend the binary product in both variables.
These are actual short exact sequences of finite-length representations. -/
def BinaryProductExactnessStatement : Prop :=
  letI := T.topology
  ∀ a b : ℕ,
    SmoothRep.PreservesFiniteLengthShortExactLeft
        (T.binaryNormalizedProductFunctor.{uF, max uF uV} a b) ∧
      SmoothRep.PreservesFiniteLengthShortExactRight
        (T.binaryNormalizedProductFunctor.{uF, max uF uV} a b)

/-- Actual induction multiplication on homogeneous exact K0, conditional only
on the separately named exactness target. Finite length is proved above. -/
def binaryProductK0 (hx : BinaryProductExactnessStatement.{uF, uV} F T) (a b : ℕ) :
    letI := T.topology
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} a F.Carrier →ₗ[ℤ]
      GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} b F.Carrier →ₗ[ℤ]
        GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} (a + b) F.Carrier :=
  letI := T.topology
  SmoothRep.FiniteLengthGrothendieckGroup.map₂
    (T.binaryNormalizedProductFunctor.{uF, max uF uV} a b)
    (binaryProduct_preservesFiniteLength F T a b) (hx a b).1 (hx a b).2

/-- The product on actual representation classes is the class of the actual
normalized induction product, not an identification of tensor and GL K0. -/
theorem binaryProductK0_classes
    (hx : BinaryProductExactnessStatement.{uF, uV} F T) (a b : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ
        (GeneralLinear a F.Carrier))
      (B : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ
        (GeneralLinear b F.Carrier)),
      binaryProductK0 F T hx a b
          (SmoothRep.FiniteLengthGrothendieckGroup.ofObject A)
          (SmoothRep.FiniteLengthGrothendieckGroup.ofObject B) =
        SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation
          ((T.binaryNormalizedProductFunctor.{uF, max uF uV} a b).obj (A.val, B.val))
          (binaryProduct_preservesFiniteLength F T a b _ _ A.property B.property) := by
  let := T.topology
  intro A B
  exact SmoothRep.FiniteLengthGrothendieckGroup.map₂_objects _ _ _ _ A B

/-- The double direct-sum extension of actual homogeneous induction products. -/
def gradedMultiplication (hx : BinaryProductExactnessStatement.{uF, uV} F T) :
    letI := T.topology
    GradedGrothendieckGroup.{uF, uV} F T →ₗ[ℤ]
      GradedGrothendieckGroup.{uF, uV} F T →ₗ[ℤ]
        GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  DirectSum.toModule ℤ ℕ _ fun a =>
    (DirectSum.toModule ℤ ℕ _ fun b =>
      ((binaryProductK0 F T hx a b).compr₂ (gradedInclusion F T (a + b))).flip).flip

@[simp]
theorem gradedMultiplication_homogeneous
    (hx : BinaryProductExactnessStatement.{uF, uV} F T) (a b : ℕ) :
    letI := T.topology
    ∀ (x : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} a F.Carrier)
      (y : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} b F.Carrier),
      gradedMultiplication F T hx (gradedInclusion F T a x) (gradedInclusion F T b y) =
        gradedInclusion F T (a + b) (binaryProductK0 F T hx a b x y) := by
  let := T.topology
  intro x y
  simp only [gradedMultiplication, gradedInclusion, DirectSum.toModule_lof,
    LinearMap.flip_apply, LinearMap.compr₂_apply]

/-- The published one-dimensional actual rank-zero unit has finite length. -/
theorem binaryProductUnit_hasFiniteLength :
    letI := T.topology
    (T.binaryProductUnit.{uF, max uF uV}).HasFiniteLength := by
  let := T.topology
  have : FiniteDimensional ℂ (T.binaryProductUnit.{uF, max uF uV}) := by
    change FiniteDimensional ℂ (ULift.{max uF uV} ℂ)
    infer_instance
  exact Derivative.ProductDerivativesFiniteLength.isFiniteLength_of_finiteDimensional _

/-- The graded unit is the class of the actual trivial line on GL_0. -/
def gradedUnit : GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  gradedInclusion F T 0
    (GeneralLinear.finiteLengthClass 0 F.Carrier
      (T.binaryProductUnit.{uF, max uF uV}) (binaryProductUnit_hasFiniteLength F T))

/-- The remaining associative, commutative and unit identities for the
constructed multiplication. Additivity is already supplied by linearity. -/
def GradedInductionRingLawsStatement
    (hx : BinaryProductExactnessStatement.{uF, uV} F T) : Prop :=
  letI := T.topology
  let m := gradedMultiplication F T hx
  (∀ x y z, m (m x y) z = m x (m y z)) ∧
    (∀ x y, m x y = m y x) ∧
    (∀ x, m (gradedUnit F T) x = x) ∧
    (∀ x, m x (gradedUnit F T) = x)

/-- Once the named representation-theoretic laws are proved, this is the
commutative ring on the actual graded exact-K0 carrier, with the constructed
induction multiplication and actual rank-zero unit. -/
@[instance_reducible]
def gradedInductionRing (hx : BinaryProductExactnessStatement.{uF, uV} F T)
    (hl : GradedInductionRingLawsStatement F T hx) :
    letI := T.topology
    CommRing (GradedGrothendieckGroup.{uF, uV} F T) := by
  let := T.topology
  exact
  { toAddCommGroup := inferInstance
    mul := fun x y => gradedMultiplication F T hx x y
    one := gradedUnit F T
    mul_assoc := hl.1
    mul_comm := hl.2.1
    one_mul := hl.2.2.1
    mul_one := hl.2.2.2
    left_distrib := fun x y z => (gradedMultiplication F T hx x).map_add y z
    right_distrib := fun x y z => (gradedMultiplication F T hx).map_add₂ x y z
    zero_mul := fun x => (gradedMultiplication F T hx).map_zero₂ x
    mul_zero := fun x => (gradedMultiplication F T hx x).map_zero }

/-- Every family of homogeneous additive operators has a canonical graded
additive extension; later comparison modules apply this to the adjusted operator. -/
def gradedOperator
    (D : letI := T.topology
      ∀ n, GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
        GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier) :
    letI := T.topology
    GradedGrothendieckGroup.{uF, uV} F T →ₗ[ℤ] GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  DirectSum.lmap D

@[simp]
theorem gradedOperator_homogeneous
    (D : letI := T.topology
      ∀ n, GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
        GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier) (n : ℕ) :
    letI := T.topology
    ∀ x, gradedOperator F T D (gradedInclusion F T n x) = gradedInclusion F T n (D n x) := by
  let := T.topology
  intro x
  exact DirectSum.lmap_lof D n x

end Langlands.Aubert
