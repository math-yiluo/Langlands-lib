import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

/-! # Valuative bounds detected by spanning trace probes -/

universe u

namespace Langlands

/-- Bounds on traces against a spanning family of probes give a common bound
on all entries of the matrices being tested. -/
def ValuativeTraceBoundStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] (N : ℕ)
    (S T : Set (Matrix (Fin N) (Fin N) F)),
    Submodule.span F T = ⊤ →
    (∀ B ∈ T, ∃ b : F, b ≠ 0 ∧ ∀ A ∈ S, (A * B).trace ≤ᵥ b) →
    ∃ b : F, b ≠ 0 ∧ ∀ A ∈ S, ∀ i j : Fin N, A i j ≤ᵥ b

end Langlands
