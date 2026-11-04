import Langlands.Representation.MatrixCoefficient.ModuloCenter
import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.DoubleCoset

/-! # L2 assembly from a finite Cartan lattice cover -/

namespace Langlands

open MeasureTheory
open scoped BigOperators ENNReal

/-- A finite Cartan lattice cover, coefficient bounds, and matching upper cell
volumes imply square integrability on the actual quotient by the full center. -/
def CartanLatticeL2Statement.{uG, uV, uI} : Prop :=
  ∀ (G : Type uG) (V : Type uV) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (I : Type uI) [Fintype I] (τ : (I → ℕ) → G) (w : I → ℝ),
    (∀ i, 0 ≤ w i) →
    ∀ (K : Subgroup G) (T : Set G), T.Finite →
      (∀ g : G, ∃ n : I → ℕ, ∃ k₁ ∈ K, ∃ t ∈ T, ∃ k₂ ∈ K,
        ∃ z ∈ Subgroup.center G, g = k₁ * τ n * t * k₂ * z) →
      ∀ (ρ : Representation ℂ G V), IsAdmissible ρ →
        ∀ (_c : UnitaryCentralCharacter ρ)
          [MeasurableSpace (G ⧸ Subgroup.center G)]
          [BorelSpace (G ⧸ Subgroup.center G)]
          (μ : Measure (G ⧸ Subgroup.center G)) [Measure.IsHaarMeasure μ],
          (∃ D : ℝ, 0 ≤ D ∧ ∀ (n : I → ℕ) (t : G), t ∈ T →
            μ ((QuotientGroup.mk : G → G ⧸ Subgroup.center G) ''
              DoubleCoset.doubleCoset (τ n * t) K K) ≤
                ENNReal.ofReal (D * ∏ i, w i ^ n i)) →
          (∀ (φ : SmoothDual ρ) (v : V),
            ∃ a : I → ℝ, (∀ i, 0 ≤ a i ∧ a i ^ 2 * w i < 1) ∧
              ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : I → ℕ) (k₁ : G), k₁ ∈ K →
                ∀ (t : G), t ∈ T → ∀ (k₂ : G), k₂ ∈ K →
                  ‖(φ : Module.Dual ℂ V) (ρ (k₁ * τ n * t * k₂) v)‖ ≤
                    C * ∏ i, a i ^ n i) →
          IsSquareIntegrableModCenter ρ μ

end Langlands
