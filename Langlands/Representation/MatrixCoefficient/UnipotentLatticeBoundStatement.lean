import Langlands.Representation.MatrixCoefficient.Definitions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Uniform-degree coefficient bounds for unipotent lattice actions -/

namespace Langlands

universe u

/-- An action of the integer lattice whose generator differences have a common
nilpotence bound has polynomially bounded coefficients of uniformly bounded
degree. The vector space need not be finite-dimensional. -/
def UnipotentLatticeCoefficientBoundStatement : Prop :=
  ∀ (d r : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin d → ℤ)) V),
    (∀ i : Fin d,
      (ρ (Multiplicative.ofAdd (Pi.single i 1)) - 1) ^ r = 0) →
    ∀ (v : V) (ell : Module.Dual ℂ V),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin d → ℤ,
        ‖matrixCoefficient ρ ell v (Multiplicative.ofAdd n)‖ ≤
          C * (1 + ∑ i, |(n i : ℝ)|) ^ (d * r)

end Langlands
