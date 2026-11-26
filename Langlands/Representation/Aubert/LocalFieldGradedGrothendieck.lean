import Langlands.Representation.Aubert.LocalFieldBinaryProductExactLengthStatement
import Langlands.Representation.Derivative.ProductDerivativesFiniteLength
import Mathlib.Algebra.DirectSum.Module

/-! # The graded exact Grothendieck multiplication over a local field -/

noncomputable section

open scoped DirectSum

namespace Langlands.Aubert.LocalFieldGraded

open AllFieldBZ.LocalFieldPackage.TopologicalData
open SmoothRep

universe uF uV

variable {K : AllFieldBZ.LocalFieldPackage.{uF}} (T : K.TopologicalData)

/-- The direct sum of the actual exact Grothendieck groups of smooth GL
representations in every natural rank. -/
abbrev GradedGrothendieckGroup :=
  letI := T.topology
  ⨁ n : ℕ, GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n K.Carrier

/-- The canonical injection of a homogeneous exact Grothendieck group. -/
def inclusion (n : ℕ) :
    letI := T.topology
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n K.Carrier →ₗ[ℤ]
      GradedGrothendieckGroup.{uF, uV} T :=
  letI := T.topology
  DirectSum.lof ℤ ℕ (fun k => GeneralLinear.FiniteLengthGrothendieckGroup k K.Carrier) n

variable (h : LocalFieldBinaryProductExactLengthStatement.{uF, uV})

/-- The bilinear map on two homogeneous groups induced by the actual binary
normalized induction functor. -/
def binaryProduct (a b : ℕ) :
    letI := T.topology
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} a K.Carrier →ₗ[ℤ]
      GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} b K.Carrier →ₗ[ℤ]
        GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} (a + b) K.Carrier :=
  letI := T.topology
  let w := h K.Carrier T a b
  FiniteLengthGrothendieckGroup.map₂
    (binaryNormalizedProductFunctor.{uF, max uF uV} T a b) w.1 w.2.1 w.2.2

/-- The two-variable direct-sum extension of the homogeneous products. -/
def multiplication :
    GradedGrothendieckGroup.{uF, uV} T →ₗ[ℤ]
      GradedGrothendieckGroup.{uF, uV} T →ₗ[ℤ]
        GradedGrothendieckGroup.{uF, uV} T :=
  letI := T.topology
  DirectSum.toModule ℤ ℕ _ fun a =>
    (DirectSum.toModule ℤ ℕ _ fun b =>
      ((binaryProduct T h a b).compr₂ (inclusion T (a + b))).flip).flip

@[simp]
theorem multiplication_homogeneous (a b : ℕ) :
    letI := T.topology
    ∀ (x : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} a K.Carrier)
      (y : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} b K.Carrier),
      multiplication T h (inclusion T a x) (inclusion T b y) =
        inclusion T (a + b) (binaryProduct T h a b x y) := by
  let := T.topology
  intro x y
  simp only [multiplication, inclusion, DirectSum.toModule_lof, LinearMap.flip_apply,
    LinearMap.compr₂_apply]

theorem binaryProduct_objects (a b : ℕ) :
    letI := T.topology
    ∀ (A : FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear a K.Carrier))
      (B : FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear b K.Carrier)),
      binaryProduct T h a b (FiniteLengthGrothendieckGroup.ofObject A)
          (FiniteLengthGrothendieckGroup.ofObject B) =
        FiniteLengthGrothendieckGroup.ofRepresentation
          ((binaryNormalizedProductFunctor T a b).obj (A.val, B.val))
          ((h K.Carrier T a b).1 _ _ A.property B.property) := by
  let := T.topology
  intro A B
  let w := h K.Carrier T a b
  exact FiniteLengthGrothendieckGroup.map₂_objects
    (binaryNormalizedProductFunctor.{uF, max uF uV} T a b) w.1 w.2.1 w.2.2 A B

/-- The actual trivial line of the rank-zero group. -/
def unitObject :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 K.Carrier) :=
  letI := T.topology
  SmoothRep.of (Representation.trivial ℂ (GeneralLinear 0 K.Carrier) (ULift.{max uF uV} ℂ))
    BinaryTensor.isSmooth_trivial

theorem unitObject_hasFiniteLength :
    letI := T.topology
    (unitObject.{uF, uV} T).HasFiniteLength := by
  let := T.topology
  let : FiniteDimensional ℂ (unitObject.{uF, uV} T) := by
    change FiniteDimensional ℂ (ULift.{max uF uV} ℂ)
    infer_instance
  exact Derivative.ProductDerivativesFiniteLength.isFiniteLength_of_finiteDimensional _

/-- The class of the trivial line in degree zero. -/
def unit : GradedGrothendieckGroup.{uF, uV} T :=
  letI := T.topology
  inclusion T 0 (FiniteLengthGrothendieckGroup.ofRepresentation (unitObject T)
    (unitObject_hasFiniteLength T))

end Langlands.Aubert.LocalFieldGraded
