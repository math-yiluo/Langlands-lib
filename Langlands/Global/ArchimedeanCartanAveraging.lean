import Langlands.Global.ArchimedeanCartanSymmetricInvariants
import Langlands.Analysis.FiniteSpanBilinear
import Langlands.Representation.AlgebraicCompactAverage
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Actual compact averaging on the Cartan symmetric algebras -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open MeasureTheory
open Langlands.Analysis.FiniteSpanIntegral
open Langlands.Representation.AlgebraicCompact
open scoped BigOperators TensorProduct Matrix.Norms.Operator

variable (K : Type u) [Field K] (n : ℕ)

/-- The actual full compact conjugation representation on the full symmetric algebra. -/
def lieSymmetricCompactRepresentation :
    _root_.Representation ℂ (standardInfiniteCompact K n) (LieSymmetricAlgebra K n) where
  toFun k := (lieSymmetricConjugation K n k.val).toAlgHom.toLinearMap
  map_one' := by
    ext P
    exact AlgEquiv.congr_fun (lieSymmetricConjugation_one K n) P
  map_mul' k l := by
    ext P
    change lieSymmetricConjugation K n (k.val * l.val) P =
      lieSymmetricConjugation K n k.val (lieSymmetricConjugation K n l.val P)
    rw [lieSymmetricConjugation_mul]
    rfl

/-- The actual full compact conjugation representation on the complementary symmetric algebra. -/
def cartanSymmetricCompactRepresentation :
    _root_.Representation ℂ (standardInfiniteCompact K n) (CartanSymmetricAlgebra K n) where
  toFun k := (cartanSymmetricConjugation K n k).toAlgHom.toLinearMap
  map_one' := by
    ext P
    exact AlgEquiv.congr_fun (cartanSymmetricConjugation_one K n) P
  map_mul' k l := by
    ext P
    change cartanSymmetricConjugation K n (k * l) P =
      cartanSymmetricConjugation K n k (cartanSymmetricConjugation K n l P)
    rw [cartanSymmetricConjugation_mul]
    rfl

variable [NumberField K]

/-- Finite matrix coordinates give finite continuous orbits for complexified real vectors. -/
theorem complexify_conjugation_hasFiniteContinuousSpan (X : RealLieAlgebra K n) :
    HasFiniteContinuousSpan (fun g : InfiniteAdelicGL K n =>
      complexLieConjugation K n g (complexify K n X)) := by
  classical
  let B := Module.finBasis ℝ (ArchimedeanMatrix K n)
  let T : ArchimedeanMatrix K n →ₗ[ℝ] ComplexLieAlgebra K n :=
    (complexify K n).toLinearMap.comp (realLieAlgebraToMatrix K n).symm.toLinearMap
  let Y : InfiniteAdelicGL K n → ArchimedeanMatrix K n := fun g =>
    (archimedeanGLCoordinates K n g).val * realLieAlgebraToMatrix K n X *
      (archimedeanGLCoordinates K n g⁻¹).val
  have hval : Continuous (fun g : InfiniteAdelicGL K n =>
      (archimedeanGLCoordinates K n g).val) :=
    Units.continuous_val.comp (archimedeanGLCoordinates K n).continuous
  have hY : Continuous Y :=
    (hval.mul continuous_const).mul (hval.comp continuous_inv)
  let c : Fin (Module.finrank ℝ (ArchimedeanMatrix K n)) → InfiniteAdelicGL K n → ℂ :=
    fun i g => (B.repr (Y g) i : ℂ)
  have hc (i : Fin (Module.finrank ℝ (ArchimedeanMatrix K n))) : Continuous (c i) :=
    Complex.continuous_ofReal.comp
      ((continuous_apply i).comp (B.continuous_coe_repr.comp hY))
  refine HasFiniteContinuousSpan.of_expansion (fun i => T (B i)) c hc ?_
  intro g
  have hgen : complexLieConjugation K n g (complexify K n X) = T (Y g) := by
    rw [complexLieConjugation_complexify, realLieConjugation_apply]
    rfl
  rw [hgen, ← B.sum_repr (Y g)]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  exact (IsScalarTower.algebraMap_smul ℂ (B.repr (Y g) i) (T (B i))).symm

/-- Every actual complex Lie vector has finite continuous conjugation span. -/
theorem complexLieConjugation_hasFiniteContinuousSpan (X : ComplexLieAlgebra K n) :
    HasFiniteContinuousSpan (fun g : InfiniteAdelicGL K n => complexLieConjugation K n g X) := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    have h : z ⊗ₜ[ℝ] X = z • complexify K n X := by
      simp only [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    simpa only [h, map_smul] using (complexify_conjugation_hasFiniteContinuousSpan K n X).smul z
  | add X Y hX hY =>
    simpa only [map_add] using hX.add hY

/-- Symmetric-algebra generation preserves the finite continuous conjugation spans. -/
theorem lieSymmetricConjugation_hasFiniteContinuousSpan (P : LieSymmetricAlgebra K n) :
    HasFiniteContinuousSpan (fun g : InfiniteAdelicGL K n => lieSymmetricConjugation K n g P) := by
  induction P using SymmetricAlgebra.induction with
  | algebraMap z =>
    simpa only [AlgEquiv.commutes] using
      (HasFiniteContinuousSpan.const (X := InfiniteAdelicGL K n)
        (algebraMap ℂ (LieSymmetricAlgebra K n) z))
  | ι X =>
    simpa only [lieSymmetricConjugation_ι] using
      (complexLieConjugation_hasFiniteContinuousSpan K n X).linearMap (SymmetricAlgebra.ι ℂ _)
  | mul P Q hP hQ =>
    simpa only [map_mul] using hP.mul hQ
  | add P Q hP hQ =>
    simpa only [map_add] using hP.add hQ

/-- Actual full symmetric compact orbits satisfy the algebraic averaging hypotheses. -/
theorem lieSymmetricCompact_hasFiniteContinuousOrbits :
    HasFiniteContinuousOrbits (lieSymmetricCompactRepresentation K n) := by
  intro P
  exact (lieSymmetricConjugation_hasFiniteContinuousSpan K n P).comp
    (fun k : standardInfiniteCompact K n => k.val) continuous_subtype_val

/-- The actual equivariant retraction transfers finite continuous orbits to the complement. -/
theorem cartanSymmetricCompact_hasFiniteContinuousOrbits :
    HasFiniteContinuousOrbits (cartanSymmetricCompactRepresentation K n) := by
  intro P
  change HasFiniteContinuousSpan (fun k : standardInfiniteCompact K n =>
    cartanSymmetricConjugation K n k P)
  have h := ((lieSymmetricCompact_hasFiniteContinuousOrbits K n)
    (cartanSymmetricInclusion K n P)).linearMap (cartanSymmetricProjection K n).toLinearMap
  change HasFiniteContinuousSpan (fun k : standardInfiniteCompact K n =>
    cartanSymmetricProjection K n
      (lieSymmetricConjugation K n k.val (cartanSymmetricInclusion K n P))) at h
  simpa only [cartanSymmetricProjection_conjugation, cartanSymmetricProjection_inclusion] using h

local instance : MeasurableSpace (standardInfiniteCompact K n) :=
  borel (standardInfiniteCompact K n)

local instance : BorelSpace (standardInfiniteCompact K n) := ⟨rfl⟩

private def cartanAveragingMeasure : Measure (standardInfiniteCompact K n) :=
  Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

local instance : IsProbabilityMeasure (cartanAveragingMeasure K n) :=
  ⟨Measure.haarMeasure_self⟩

local instance : (cartanAveragingMeasure K n).IsMulLeftInvariant := by
  dsimp only [cartanAveragingMeasure]
  infer_instance

/-- Normalized Haar averaging into the actual full symmetric compact fixed algebra. -/
def lieSymmetricCompactAverage :
    LieSymmetricAlgebra K n →ₗ[ℂ] lieSymmetricCompactInvariants K n :=
  (average (lieSymmetricCompactRepresentation K n)
    (lieSymmetricCompact_hasFiniteContinuousOrbits K n) (cartanAveragingMeasure K n)).codRestrict
      (lieSymmetricCompactInvariants K n).toSubmodule
      (average_mem_invariants (lieSymmetricCompactRepresentation K n)
        (lieSymmetricCompact_hasFiniteContinuousOrbits K n) (cartanAveragingMeasure K n))

/-- Normalized Haar averaging into the actual complementary compact fixed algebra. -/
def cartanSymmetricCompactAverage :
    CartanSymmetricAlgebra K n →ₗ[ℂ] cartanSymmetricCompactInvariants K n :=
  (average (cartanSymmetricCompactRepresentation K n)
    (cartanSymmetricCompact_hasFiniteContinuousOrbits K n)
      (cartanAveragingMeasure K n)).codRestrict
      (cartanSymmetricCompactInvariants K n).toSubmodule
      (average_mem_invariants (cartanSymmetricCompactRepresentation K n)
        (cartanSymmetricCompact_hasFiniteContinuousOrbits K n) (cartanAveragingMeasure K n))

@[simp]
theorem lieSymmetricCompactAverage_fixed (P : lieSymmetricCompactInvariants K n) :
    lieSymmetricCompactAverage K n P.val = P := by
  apply Subtype.ext
  exact average_fixed (lieSymmetricCompactRepresentation K n)
    (lieSymmetricCompact_hasFiniteContinuousOrbits K n) (cartanAveragingMeasure K n)
    P.val P.property

@[simp]
theorem cartanSymmetricCompactAverage_fixed (P : cartanSymmetricCompactInvariants K n) :
    cartanSymmetricCompactAverage K n P.val = P := by
  apply Subtype.ext
  exact average_fixed (cartanSymmetricCompactRepresentation K n)
    (cartanSymmetricCompact_hasFiniteContinuousOrbits K n) (cartanAveragingMeasure K n)
    P.val P.property

/-- The actual inclusion commutes with normalized averaging. -/
@[simp]
theorem lieSymmetricCompactAverage_inclusion (P : CartanSymmetricAlgebra K n) :
    lieSymmetricCompactAverage K n (cartanSymmetricInclusion K n P) =
      cartanCompactInvariantInclusion K n (cartanSymmetricCompactAverage K n P) := by
  apply Subtype.ext
  exact average_natural (cartanSymmetricCompactRepresentation K n)
    (cartanSymmetricCompact_hasFiniteContinuousOrbits K n) (cartanAveragingMeasure K n)
    (lieSymmetricCompactRepresentation K n) (lieSymmetricCompact_hasFiniteContinuousOrbits K n)
    (cartanSymmetricInclusion K n).toLinearMap
    (fun k Q => cartanSymmetricInclusion_conjugation K n k Q) P

/-- The actual projection commutes with normalized averaging. -/
@[simp]
theorem cartanSymmetricCompactAverage_projection (P : LieSymmetricAlgebra K n) :
    cartanSymmetricCompactAverage K n (cartanSymmetricProjection K n P) =
      cartanCompactInvariantProjection K n (lieSymmetricCompactAverage K n P) := by
  apply Subtype.ext
  exact average_natural (lieSymmetricCompactRepresentation K n)
    (lieSymmetricCompact_hasFiniteContinuousOrbits K n) (cartanAveragingMeasure K n)
    (cartanSymmetricCompactRepresentation K n)
    (cartanSymmetricCompact_hasFiniteContinuousOrbits K n)
    (cartanSymmetricProjection K n).toLinearMap
    (fun k Q => cartanSymmetricProjection_conjugation K n k Q) P

/-- A full symmetric invariant factor can be pulled out of the average. -/
theorem lieSymmetricCompactAverage_mul_left
    (P : lieSymmetricCompactInvariants K n) (Q : LieSymmetricAlgebra K n) :
    lieSymmetricCompactAverage K n (P.val * Q) = P * lieSymmetricCompactAverage K n Q := by
  apply Subtype.ext
  apply average_natural (lieSymmetricCompactRepresentation K n)
    (lieSymmetricCompact_hasFiniteContinuousOrbits K n) (cartanAveragingMeasure K n)
    (lieSymmetricCompactRepresentation K n) (lieSymmetricCompact_hasFiniteContinuousOrbits K n)
    ((LinearMap.mul ℂ (LieSymmetricAlgebra K n)) P.val)
  intro k R
  change P.val * lieSymmetricConjugation K n k.val R =
    lieSymmetricConjugation K n k.val (P.val * R)
  rw [map_mul, P.property k]

/-- A complementary invariant factor can be pulled out of the average. -/
theorem cartanSymmetricCompactAverage_mul_left
    (P : cartanSymmetricCompactInvariants K n) (Q : CartanSymmetricAlgebra K n) :
    cartanSymmetricCompactAverage K n (P.val * Q) = P * cartanSymmetricCompactAverage K n Q := by
  apply Subtype.ext
  apply average_natural (cartanSymmetricCompactRepresentation K n)
    (cartanSymmetricCompact_hasFiniteContinuousOrbits K n) (cartanAveragingMeasure K n)
    (cartanSymmetricCompactRepresentation K n)
    (cartanSymmetricCompact_hasFiniteContinuousOrbits K n)
    ((LinearMap.mul ℂ (CartanSymmetricAlgebra K n)) P.val)
  intro k R
  change P.val * cartanSymmetricConjugation K n k R =
    cartanSymmetricConjugation K n k (P.val * R)
  rw [map_mul, P.property k]

/-- The full symmetric Reynolds retraction is linear over its actual fixed algebra. -/
def lieSymmetricCompactReynolds :
    LieSymmetricAlgebra K n →ₗ[lieSymmetricCompactInvariants K n]
      lieSymmetricCompactInvariants K n where
  toFun := lieSymmetricCompactAverage K n
  map_add' := (lieSymmetricCompactAverage K n).map_add
  map_smul' P Q := lieSymmetricCompactAverage_mul_left K n P Q

/-- The complementary Reynolds retraction is linear over its actual fixed algebra. -/
def cartanSymmetricCompactReynolds :
    CartanSymmetricAlgebra K n →ₗ[cartanSymmetricCompactInvariants K n]
      cartanSymmetricCompactInvariants K n where
  toFun := cartanSymmetricCompactAverage K n
  map_add' := (cartanSymmetricCompactAverage K n).map_add
  map_smul' P Q := cartanSymmetricCompactAverage_mul_left K n P Q

@[simp]
theorem lieSymmetricCompactReynolds_apply (P : LieSymmetricAlgebra K n) :
    lieSymmetricCompactReynolds K n P = lieSymmetricCompactAverage K n P := rfl

@[simp]
theorem cartanSymmetricCompactReynolds_apply (P : CartanSymmetricAlgebra K n) :
    cartanSymmetricCompactReynolds K n P = cartanSymmetricCompactAverage K n P := rfl

end Langlands.Global.ArchimedeanGL
