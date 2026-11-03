import Langlands.Representation.Smooth.Definitions
import Langlands.Representation.Exponents.Central
import Mathlib.Basic.Complex.Basic

/-!
# Detecting a full-center exponent from one central operator

This derived statement isolates the finite-dimensional spectral step needed
for strict Jacquet bounds. It asserts no decomposition of the representation.
-/

namespace Langlands

universe uG uV

/-- Every generalized eigenvalue of one central operator on an admissible
complex representation occurs as the value of a smooth full-center exponent. -/
def CentralEigenvalueDetectionStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V), IsAdmissible ρ →
    ∀ (z : Subgroup.center G) (μ : ℂ) (n : ℕ) (v : V),
      v ≠ 0 → ((ρ (z : G) - μ • 1) ^ n) v = 0 →
      ∃ χ : Subgroup.center G →* ℂˣ, IsCentralExponent ρ χ ∧ (χ z : ℂ) = μ

end Langlands
