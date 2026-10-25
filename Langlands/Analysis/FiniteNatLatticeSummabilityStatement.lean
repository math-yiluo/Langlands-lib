import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Polynomial-geometric summability on finite natural-number lattices -/

namespace Langlands

open scoped BigOperators ENNReal

/-- Real summability of a polynomial height times coordinatewise geometric
decay, for every finite index type, including the empty type. -/
def FiniteNatLatticeRealSummabilityStatement.{uI} : Prop :=
  ∀ (I : Type uI) [Fintype I] (r : I → ℝ),
    (∀ i, 0 ≤ r i) → (∀ i, r i < 1) →
    ∀ (s : ℝ), 0 ≤ s →
      Summable (fun k : I → ℕ =>
        Real.rpow (1 + ∑ i, (k i : ℝ)) s * ∏ i, (r i) ^ (k i))

/-- Finiteness of the ENNReal sum of the same polynomial-geometric summand. -/
def FiniteNatLatticeENNRealSummabilityStatement.{uI} : Prop :=
  ∀ (I : Type uI) [Fintype I] (r : I → ℝ),
    (∀ i, 0 ≤ r i) → (∀ i, r i < 1) →
    ∀ (s : ℝ), 0 ≤ s →
      (∑' k : I → ℕ, ENNReal.ofReal
        (Real.rpow (1 + ∑ i, (k i : ℝ)) s * ∏ i, (r i) ^ (k i))) < ∞

/-- Elementary real and ENNReal summability targets for polynomial-geometric
weights on arbitrary finite natural-number lattices. -/
def FiniteNatLatticeSummabilityStatement.{uI} : Prop :=
  FiniteNatLatticeRealSummabilityStatement.{uI} ∧
    FiniteNatLatticeENNRealSummabilityStatement.{uI}

end Langlands
