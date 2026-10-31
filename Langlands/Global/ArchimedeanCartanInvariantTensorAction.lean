import Langlands.Global.ArchimedeanCartanTensorAction
import Langlands.Representation.AlgebraicCompactLifting

/-! # Degree-bounded invariant lifts for actual Cartan tensor actions -/

noncomputable section
universe u w
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open MeasureTheory
open Langlands.Representation.AlgebraicCompact

variable (K : Type u) [Field K] (n : ℕ)

section Module

variable {V : Type w} [AddCommGroup V] [Module ℂ V]
  [Module (EnvelopingAlgebra K n) V] [IsScalarTower ℂ (EnvelopingAlgebra K n) V]

/-- Restrict the actual Cartan tensor action to fixed source and target vectors. -/
def cartanInvariantTensorAction (τ : ContinuousCompactRep K n)
    (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V)
    (ρ : _root_.Representation ℂ (standardInfiniteCompact K n) V)
    (hj : ∀ k v, j (τ.toRepresentation k v) = ρ k (j v))
    (hρ : ∀ k a v, ρ k (a • v) = envelopingConjugation K n k.val a • ρ k v) :
    cartanSymmetricCovariants K n τ →ₗ[ℂ] ρ.invariants :=
  ((cartanTensorAction K n τ j).comp
    ((cartanSymmetricCovariants K n τ).restrictScalars ℂ).subtype).codRestrict
      ρ.invariants (by
        intro x k
        change ρ k (cartanTensorAction K n τ j x.val) =
          cartanTensorAction K n τ j x.val
        rw [← cartanTensorAction_equivariant K n τ j ρ hj hρ, x.property k])

@[simp]
theorem cartanInvariantTensorAction_coe (τ : ContinuousCompactRep K n)
    (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V)
    (ρ : _root_.Representation ℂ (standardInfiniteCompact K n) V)
    (hj : ∀ k v, j (τ.toRepresentation k v) = ρ k (j v))
    (hρ : ∀ k a v, ρ k (a • v) = envelopingConjugation K n k.val a • ρ k v)
    (x : cartanSymmetricCovariants K n τ) :
    (cartanInvariantTensorAction K n τ j ρ hj hρ x : V) =
      cartanTensorAction K n τ j x.val := rfl

end Module

variable [NumberField K]

local instance invariantTensorMeasurableSpace :
    MeasurableSpace (standardInfiniteCompact K n) := borel _
local instance invariantTensorBorelSpace : BorelSpace (standardInfiniteCompact K n) := ⟨rfl⟩

private def invariantTensorMeasure : Measure (standardInfiniteCompact K n) :=
  Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

local instance invariantTensorProbabilityMeasure :
    IsProbabilityMeasure (invariantTensorMeasure K n) := ⟨Measure.haarMeasure_self⟩

/-- The actual compact covariant average retains the actual tensor degree bound. -/
theorem cartanSymmetricCovariantAverage_mem_degreeFiltration
    (τ : ContinuousCompactRep K n) {d : ℕ} {x : CartanSymmetricCovariantModule K n τ}
    (hx : x ∈ cartanSymmetricTensorDegreeFiltration K n τ d) :
    (cartanSymmetricCovariantAverage K n τ x).val ∈
      cartanSymmetricTensorDegreeFiltration K n τ d := by
  change average (cartanSymmetricCovariantRepresentation K n τ)
    (cartanSymmetricCovariant_hasFiniteContinuousOrbits K n τ)
    (invariantTensorMeasure K n) x ∈ cartanSymmetricTensorDegreeFiltration K n τ d
  exact average_mem_submodule _ _ _ _ x (fun k =>
    cartanSymmetricCovariantRepresentation_mem_degreeFiltration K n τ k hx)

section Module

variable {V : Type w} [AddCommGroup V] [Module ℂ V]
  [Module (EnvelopingAlgebra K n) V] [IsScalarTower ℂ (EnvelopingAlgebra K n) V]

/-- Averaging an actual Cartan tensor with fixed image retains that image. -/
theorem cartanTensorAction_average_eq_of_fixed (τ : ContinuousCompactRep K n)
    (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V)
    (ρ : _root_.Representation ℂ (standardInfiniteCompact K n) V)
    (hj : ∀ k v, j (τ.toRepresentation k v) = ρ k (j v))
    (hρ : ∀ k a v, ρ k (a • v) = envelopingConjugation K n k.val a • ρ k v)
    (x : CartanSymmetricCovariantModule K n τ)
    (hx : cartanTensorAction K n τ j x ∈ ρ.invariants) :
    cartanTensorAction K n τ j (cartanSymmetricCovariantAverage K n τ x).val =
      cartanTensorAction K n τ j x := by
  change cartanTensorAction K n τ j
    (average (cartanSymmetricCovariantRepresentation K n τ)
      (cartanSymmetricCovariant_hasFiniteContinuousOrbits K n τ)
      (invariantTensorMeasure K n) x) = cartanTensorAction K n τ j x
  apply map_average_eq_of_orbit_constant
  intro k
  rw [cartanTensorAction_equivariant K n τ j ρ hj hρ]
  exact hx k

/-- A fixed vector in a bounded Cartan orbit span has a fixed tensor preimage
with the same actual degree bound. -/
theorem exists_cartanInvariantTensorAction_preimage_degree
    (τ : ContinuousCompactRep K n) (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V)
    (ρ : _root_.Representation ℂ (standardInfiniteCompact K n) V)
    (hj : ∀ k v, j (τ.toRepresentation k v) = ρ k (j v))
    (hρ : ∀ k a v, ρ k (a • v) = envelopingConjugation K n k.val a • ρ k v)
    (d : ℕ) (y : ρ.invariants)
    (hy : y.val ∈ cartanSymmetrizationSpan K n d • LinearMap.range j) :
    ∃ x : cartanSymmetricCovariants K n τ,
      x.val ∈ cartanSymmetricTensorDegreeFiltration K n τ d ∧
      cartanInvariantTensorAction K n τ j ρ hj hρ x = y := by
  rw [← cartanTensorAction_map_degreeFiltration K n τ j d] at hy
  obtain ⟨x, hx, heq⟩ := hy
  have hfixed : cartanTensorAction K n τ j x ∈ ρ.invariants := heq.symm ▸ y.property
  refine ⟨cartanSymmetricCovariantAverage K n τ x,
    cartanSymmetricCovariantAverage_mem_degreeFiltration K n τ hx, ?_⟩
  apply Subtype.ext
  exact (cartanTensorAction_average_eq_of_fixed K n τ j ρ hj hρ x hfixed).trans heq

/-- Compact-generator stability upgrades bounded invariant lifting to the full
genuine enveloping filtered orbit span. -/
theorem exists_cartanInvariantTensorAction_preimage_envelopingDegree
    (τ : ContinuousCompactRep K n) (j : (Fin τ.dim → ℂ) →ₗ[ℂ] V)
    (ρ : _root_.Representation ℂ (standardInfiniteCompact K n) V)
    (hj : ∀ k v, j (τ.toRepresentation k v) = ρ k (j v))
    (hρ : ∀ k a v, ρ k (a • v) = envelopingConjugation K n k.val a • ρ k v)
    (hstable : ∀ X : CompactComplexLieAlgebra K n, ∀ w ∈ LinearMap.range j,
      compactEnvelopingGenerator K n X • w ∈ LinearMap.range j)
    (d : ℕ) (y : ρ.invariants)
    (hy : y.val ∈ envelopingDegreeFiltration K n d • LinearMap.range j) :
    ∃ x : cartanSymmetricCovariants K n τ,
      x.val ∈ cartanSymmetricTensorDegreeFiltration K n τ d ∧
      cartanInvariantTensorAction K n τ j ρ hj hρ x = y := by
  apply exists_cartanInvariantTensorAction_preimage_degree K n τ j ρ hj hρ d y
  rw [cartanSymmetrizationSpan_smul_eq K n (LinearMap.range j) hstable]
  exact hy

end Module

end Langlands.Global.ArchimedeanGL
