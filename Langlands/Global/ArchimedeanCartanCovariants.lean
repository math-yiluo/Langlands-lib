import Langlands.Global.ArchimedeanCartanAveraging
import Langlands.Global.ArchimedeanCompactTypes
import Langlands.Algebra.ReynoldsCovariants
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Algebra.Tower

/-! # Actual compact covariants of the Cartan symmetric algebra -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open MeasureTheory
open Langlands.Analysis.FiniteSpanIntegral
open Langlands.Representation.AlgebraicCompact
open scoped TensorProduct

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The actual complementary symmetric algebra tensored with a compact representation. -/
abbrev CartanSymmetricCovariantModule (τ : ContinuousCompactRep K n) :=
  CartanSymmetricAlgebra K n ⊗[ℂ] (Fin τ.dim → ℂ)

/-- The diagonal full compact action on the actual complementary tensor module. -/
def cartanSymmetricCovariantRepresentation (τ : ContinuousCompactRep K n) :
    _root_.Representation ℂ (standardInfiniteCompact K n) (CartanSymmetricCovariantModule K n τ) :=
  (cartanSymmetricCompactRepresentation K n).tprod τ.toRepresentation

omit [NumberField K] in
@[simp]
theorem cartanSymmetricCovariantRepresentation_tmul (τ : ContinuousCompactRep K n)
    (k : standardInfiniteCompact K n) (P : CartanSymmetricAlgebra K n) (v : Fin τ.dim → ℂ) :
    cartanSymmetricCovariantRepresentation K n τ k (P ⊗ₜ[ℂ] v) =
      cartanSymmetricConjugation K n k P ⊗ₜ[ℂ] τ.toRepresentation k v :=
  TensorProduct.map_tmul _ _ P v

omit [NumberField K] in
/-- The diagonal action is semilinear for the actual coefficient conjugation. -/
theorem cartanSymmetricCovariantRepresentation_smul (τ : ContinuousCompactRep K n)
    (k : standardInfiniteCompact K n) (P : CartanSymmetricAlgebra K n)
    (x : CartanSymmetricCovariantModule K n τ) :
    cartanSymmetricCovariantRepresentation K n τ k (P • x) =
      cartanSymmetricConjugation K n k P • cartanSymmetricCovariantRepresentation K n τ k x := by
  induction x using TensorProduct.inductionOn with
  | tmul Q v =>
    simp only [TensorProduct.smul_tmul', smul_eq_mul,
      cartanSymmetricCovariantRepresentation_tmul, map_mul]
  | add x y hx hy =>
    simp only [smul_add, map_add, hx, hy]

omit [NumberField K] in
/-- Every orbit in a finite-dimensional continuous compact representation has finite continuous span. -/
theorem ContinuousCompactRep.hasFiniteContinuousOrbits (τ : ContinuousCompactRep K n) :
    HasFiniteContinuousOrbits τ.toRepresentation := by
  intro v
  refine ⟨IsNoetherian.noetherian _, ?_⟩
  intro l
  exact l.continuous_of_finiteDimensional.comp (τ.continuous_orbit v)

/-- The actual tensor representation satisfies the finite-span averaging hypotheses. -/
theorem cartanSymmetricCovariant_hasFiniteContinuousOrbits (τ : ContinuousCompactRep K n) :
    HasFiniteContinuousOrbits (cartanSymmetricCovariantRepresentation K n τ) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul P v =>
    change HasFiniteContinuousSpan (fun k : standardInfiniteCompact K n =>
      cartanSymmetricConjugation K n k P ⊗ₜ[ℂ] τ.toRepresentation k v)
    exact ((cartanSymmetricCompact_hasFiniteContinuousOrbits K n) P).bilinear
      (τ.hasFiniteContinuousOrbits K n v)
      (TensorProduct.mk ℂ (CartanSymmetricAlgebra K n) (Fin τ.dim → ℂ))
  | add x y hx hy =>
    simpa only [map_add] using hx.add hy

/-- Actual full compact fixed tensors, as a module over the actual fixed coefficient algebra. -/
def cartanSymmetricCovariants (τ : ContinuousCompactRep K n) :
    Submodule (cartanSymmetricCompactInvariants K n) (CartanSymmetricCovariantModule K n τ) where
  carrier := {x | ∀ k : standardInfiniteCompact K n,
    cartanSymmetricCovariantRepresentation K n τ k x = x}
  zero_mem' := by intro k; exact map_zero _
  add_mem' := by intro x y hx hy k; simp only [map_add, hx k, hy k]
  smul_mem' := by
    intro a x hx k
    change cartanSymmetricCovariantRepresentation K n τ k (a.val • x) = a.val • x
    rw [cartanSymmetricCovariantRepresentation_smul, a.property k, hx k]

omit [NumberField K] in
@[simp]
theorem mem_cartanSymmetricCovariants (τ : ContinuousCompactRep K n)
    (x : CartanSymmetricCovariantModule K n τ) :
    x ∈ cartanSymmetricCovariants K n τ ↔
      ∀ k : standardInfiniteCompact K n, cartanSymmetricCovariantRepresentation K n τ k x = x :=
  Iff.rfl

local instance (τ : ContinuousCompactRep K n) :
    SMul (cartanSymmetricCompactInvariants K n) (cartanSymmetricCovariants K n τ) :=
  (Submodule.module (cartanSymmetricCovariants K n τ)).toSMul

local instance : MeasurableSpace (standardInfiniteCompact K n) :=
  borel (standardInfiniteCompact K n)

local instance : BorelSpace (standardInfiniteCompact K n) := ⟨rfl⟩

private def cartanCovariantMeasure : Measure (standardInfiniteCompact K n) :=
  Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

local instance : IsProbabilityMeasure (cartanCovariantMeasure K n) :=
  ⟨Measure.haarMeasure_self⟩

local instance : (cartanCovariantMeasure K n).IsMulLeftInvariant := by
  dsimp only [cartanCovariantMeasure]
  infer_instance

/-- Normalized Haar average onto the actual full compact covariants. -/
def cartanSymmetricCovariantAverage (τ : ContinuousCompactRep K n) :
    CartanSymmetricCovariantModule K n τ →ₗ[ℂ] cartanSymmetricCovariants K n τ :=
  (average (cartanSymmetricCovariantRepresentation K n τ)
    (cartanSymmetricCovariant_hasFiniteContinuousOrbits K n τ)
    (cartanCovariantMeasure K n)).codRestrict
      ((cartanSymmetricCovariants K n τ).restrictScalars ℂ)
      (average_mem_invariants (cartanSymmetricCovariantRepresentation K n τ)
        (cartanSymmetricCovariant_hasFiniteContinuousOrbits K n τ) (cartanCovariantMeasure K n))

@[simp]
theorem cartanSymmetricCovariantAverage_fixed (τ : ContinuousCompactRep K n)
    (x : cartanSymmetricCovariants K n τ) :
    cartanSymmetricCovariantAverage K n τ x.val = x := by
  apply Subtype.ext
  exact average_fixed (cartanSymmetricCovariantRepresentation K n τ)
    (cartanSymmetricCovariant_hasFiniteContinuousOrbits K n τ) (cartanCovariantMeasure K n)
    x.val x.property

/-- Multiplication by a fixed coefficient commutes with covariant averaging. -/
theorem cartanSymmetricCovariantAverage_smul
    (τ : ContinuousCompactRep K n) (a : cartanSymmetricCompactInvariants K n)
    (x : CartanSymmetricCovariantModule K n τ) :
    cartanSymmetricCovariantAverage K n τ (a • x) =
      a • cartanSymmetricCovariantAverage K n τ x := by
  apply Subtype.ext
  apply average_natural (cartanSymmetricCovariantRepresentation K n τ)
    (cartanSymmetricCovariant_hasFiniteContinuousOrbits K n τ) (cartanCovariantMeasure K n)
    (cartanSymmetricCovariantRepresentation K n τ)
    (cartanSymmetricCovariant_hasFiniteContinuousOrbits K n τ)
    (Algebra.lsmul ℂ ℂ (CartanSymmetricCovariantModule K n τ) a.val)
  intro k y
  change a.val • cartanSymmetricCovariantRepresentation K n τ k y =
    cartanSymmetricCovariantRepresentation K n τ k (a.val • y)
  rw [cartanSymmetricCovariantRepresentation_smul, a.property k]

/-- The actual covariant projection is linear over the actual compact fixed algebra. -/
def cartanSymmetricCovariantReynolds (τ : ContinuousCompactRep K n) :
    CartanSymmetricCovariantModule K n τ →ₗ[cartanSymmetricCompactInvariants K n]
      cartanSymmetricCovariants K n τ where
  toFun := cartanSymmetricCovariantAverage K n τ
  map_add' := (cartanSymmetricCovariantAverage K n τ).map_add
  map_smul' := cartanSymmetricCovariantAverage_smul K n τ

@[simp]
theorem cartanSymmetricCovariantReynolds_apply (τ : ContinuousCompactRep K n)
    (x : CartanSymmetricCovariantModule K n τ) :
    cartanSymmetricCovariantReynolds K n τ x =
      cartanSymmetricCovariantAverage K n τ x := rfl

/-- An arbitrary coefficient times a fixed tensor averages by averaging the coefficient. -/
theorem cartanSymmetricCovariantAverage_coefficient
    (τ : ContinuousCompactRep K n) (P : CartanSymmetricAlgebra K n)
    (x : cartanSymmetricCovariants K n τ) :
    cartanSymmetricCovariantAverage K n τ (P • x.val) =
      cartanSymmetricCompactAverage K n P • x := by
  apply Subtype.ext
  apply average_natural (cartanSymmetricCompactRepresentation K n)
    (cartanSymmetricCompact_hasFiniteContinuousOrbits K n) (cartanCovariantMeasure K n)
    (cartanSymmetricCovariantRepresentation K n τ)
    (cartanSymmetricCovariant_hasFiniteContinuousOrbits K n τ)
    ((LinearMap.toSpanSingleton (CartanSymmetricAlgebra K n)
      (CartanSymmetricCovariantModule K n τ) x.val).restrictScalars ℂ)
  intro k Q
  change cartanSymmetricConjugation K n k Q • x.val =
    cartanSymmetricCovariantRepresentation K n τ k (Q • x.val)
  rw [cartanSymmetricCovariantRepresentation_smul, x.property k]

/-- The actual coefficient and module averages form a compatible Reynolds pair. -/
def cartanSymmetricCovariantReynoldsPair (τ : ContinuousCompactRep K n) :
    Langlands.Algebra.ReynoldsPair
      (cartanSymmetricCompactInvariants K n) (CartanSymmetricAlgebra K n)
      (CartanSymmetricCovariantModule K n τ) (cartanSymmetricCovariants K n τ) where
  coefficient := cartanSymmetricCompactReynolds K n
  projection := cartanSymmetricCovariantReynolds K n τ
  projection_fixed := cartanSymmetricCovariantAverage_fixed K n τ
  projection_smul := cartanSymmetricCovariantAverage_coefficient K n τ

/-- Actual finite-dimensional compact covariants are finite over the compact fixed algebra. -/
theorem cartanSymmetricCovariants_moduleFinite (τ : ContinuousCompactRep K n) :
    Module.Finite (cartanSymmetricCompactInvariants K n) (cartanSymmetricCovariants K n τ) :=
  (cartanSymmetricCovariantReynoldsPair K n τ).moduleFinite_of_noetherianRing

end Langlands.Global.ArchimedeanGL
