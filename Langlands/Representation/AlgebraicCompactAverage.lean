import Langlands.Analysis.FiniteSpanIntegral
import Mathlib.RepresentationTheory.Invariants
import Mathlib.MeasureTheory.Group.Integral

/-! # Compact averaging for algebraically locally finite representations -/

noncomputable section
universe uG uV uW
set_option autoImplicit false

namespace Langlands.Representation.AlgebraicCompact

open MeasureTheory MeasureTheory.Measure
open Langlands.Analysis.FiniteSpanIntegral

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Every orbit has finite-dimensional algebraic span and continuous scalar coefficients. -/
def HasFiniteContinuousOrbits (ρ : _root_.Representation ℂ G V) : Prop :=
  ∀ v : V, HasFiniteContinuousSpan (fun g : G => ρ g v)

variable [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (ρ : _root_.Representation ℂ G V) (hρ : HasFiniteContinuousOrbits ρ)
  (μ : Measure G) [IsFiniteMeasure μ]

/-- Compact averaging constructed by scalar integration in each finite orbit span. -/
def average : V →ₗ[ℂ] V where
  toFun v := Langlands.Analysis.FiniteSpanIntegral.integral μ (fun g => ρ g v) (hρ v)
  map_add' v w := by
    apply eq_of_dual_eq
    intro l
    simp only [dual_integral, map_add]
    exact MeasureTheory.integral_add ((hρ v).integrable_dual μ l)
      ((hρ w).integrable_dual μ l)
  map_smul' c v := by
    apply eq_of_dual_eq
    intro l
    simp only [dual_integral, map_smul, RingHom.id_apply]
    exact MeasureTheory.integral_smul c (fun g => l (ρ g v))

@[simp]
theorem dual_average (v : V) (l : Module.Dual ℂ V) :
    l (average ρ hρ μ v) = ∫ g, l (ρ g v) ∂μ :=
  dual_integral μ _ (hρ v) l

/-- Left invariance of the measure makes the average a fixed vector. -/
theorem average_mem_invariants [MeasurableMul G] [IsMulLeftInvariant μ] (v : V) :
    average ρ hρ μ v ∈ ρ.invariants := by
  intro k
  apply eq_of_dual_eq
  intro l
  calc
    l (ρ k (average ρ hρ μ v)) = ∫ g, l (ρ k (ρ g v)) ∂μ :=
      dual_average ρ hρ μ v (l.comp (ρ k))
    _ = ∫ g, l (ρ (k * g) v) ∂μ := by simp only [map_mul, Module.End.mul_apply]
    _ = ∫ g, l (ρ g v) ∂μ := integral_mul_left_eq_self (fun g => l (ρ g v)) k
    _ = l (average ρ hρ μ v) := (dual_average ρ hρ μ v l).symm

/-- A normalized average retracts every fixed vector. -/
theorem average_fixed [IsProbabilityMeasure μ] (v : V) (hv : v ∈ ρ.invariants) :
    average ρ hρ μ v = v := by
  apply eq_of_dual_eq
  intro l
  rw [dual_average]
  change ∀ g : G, ρ g v = v at hv
  simp [hv]

/-- The actual linear projection onto the submodule of fixed vectors. -/
def averageToInvariants [MeasurableMul G] [IsMulLeftInvariant μ] : V →ₗ[ℂ] ρ.invariants :=
  (average ρ hρ μ).codRestrict ρ.invariants (average_mem_invariants ρ hρ μ)

@[simp]
theorem averageToInvariants_coe [MeasurableMul G] [IsMulLeftInvariant μ] (v : V) :
    (averageToInvariants ρ hρ μ v : V) = average ρ hρ μ v := rfl

@[simp]
theorem averageToInvariants_fixed [MeasurableMul G] [IsMulLeftInvariant μ]
    [IsProbabilityMeasure μ] (v : ρ.invariants) :
    averageToInvariants ρ hρ μ v.val = v := by
  apply Subtype.ext
  exact average_fixed ρ hρ μ v.val v.property

/-- Averaging commutes with every equivariant algebraic linear map. -/
theorem average_natural (σ : _root_.Representation ℂ G W) (hσ : HasFiniteContinuousOrbits σ)
    (L : V →ₗ[ℂ] W) (hL : ∀ (g : G) (v : V), L (ρ g v) = σ g (L v)) (v : V) :
    average σ hσ μ (L v) = L (average ρ hρ μ v) := by
  apply eq_of_dual_eq
  intro l
  calc
    l (average σ hσ μ (L v)) = ∫ g, l (σ g (L v)) ∂μ := dual_average σ hσ μ (L v) l
    _ = ∫ g, l (L (ρ g v)) ∂μ := by simp only [hL]
    _ = l (L (average ρ hρ μ v)) := (dual_average ρ hρ μ v (l.comp L)).symm

end Langlands.Representation.AlgebraicCompact
