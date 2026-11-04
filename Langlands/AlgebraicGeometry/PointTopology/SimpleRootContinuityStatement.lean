import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Normed.Field.Basic

/-! # Local continuity of a simple root in a monic polynomial family -/

noncomputable section

universe u

open Filter
open scoped Topology BigOperators

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The local root branch needed for smooth point-map openness, with local uniqueness. -/
def MonicSimpleRootContinuityStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (n : ℕ) (_hn : 0 < n),
      let p : (Fin n → K) → Polynomial K :=
        fun c => Polynomial.X ^ n +
          ∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ i.val
      ∀ (c : Fin n → K) (a : K),
        (p c).eval a = 0 → (p c).derivative.eval a ≠ 0 →
        ∃ ψ : (Fin n → K) → K,
          ψ c = a ∧ ContinuousAt ψ c ∧
          (∀ᶠ C in 𝓝 c, (p C).eval (ψ C) = 0 ∧ (p C).derivative.eval (ψ C) ≠ 0) ∧
          (∀ᶠ v in 𝓝 (c, a), (p v.1).eval v.2 = 0 ↔ ψ v.1 = v.2)

end Langlands.AlgebraicGeometry.PointTopology
