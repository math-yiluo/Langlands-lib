import Langlands.Representation.Smooth.Contragredient.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Group.Basic

/-! # Product coefficient bounds on compact translates of a lattice -/

open scoped BigOperators

namespace Langlands

universe uG uV uI

/-- Product coefficient decay with fixed coordinate weights extends uniformly
over two compact translates and a finite middle translate. -/
def CompactTranslateLatticeBoundStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V), IsSmooth ρ →
    ∀ (I : Type uI) [Fintype I] (τ : (I → ℕ) → G) (w : I → ℝ),
      (∀ (φ : SmoothDual ρ) (v : V),
        ∃ a : I → ℝ, (∀ i, 0 < a i ∧ a i ^ 2 * w i < 1) ∧
          ∃ C : ℝ, 0 < C ∧ ∀ n : I → ℕ,
            ‖(φ : Module.Dual ℂ V) (ρ (τ n) v)‖ ≤ C * ∏ i, a i ^ n i) →
      ∀ (S₁ S₂ T : Set G), IsCompact S₁ → IsCompact S₂ → T.Finite →
        ∀ (φ : SmoothDual ρ) (v : V),
          ∃ a : I → ℝ, (∀ i, 0 < a i ∧ a i ^ 2 * w i < 1) ∧
            ∃ C : ℝ, 0 < C ∧ ∀ (n : I → ℕ)
              (k₁ : G), k₁ ∈ S₁ → ∀ (t : G), t ∈ T →
              ∀ (k₂ : G), k₂ ∈ S₂ →
                ‖(φ : Module.Dual ℂ V) (ρ (k₁ * τ n * t * k₂) v)‖ ≤
                  C * ∏ i, a i ^ n i

end Langlands
