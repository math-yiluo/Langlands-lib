import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Basis.Defs

/-! # Ordered monomials in the actual universal enveloping algebra -/

noncomputable section

universe u v

set_option autoImplicit false

namespace Langlands.Algebra.UniversalEnveloping

variable {k : Type u} {L : Type v} [Field k] [LieRing L] [LieAlgebra k L]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Multiply the powers of the actual Lie generators in ascending basis-index order. -/
def orderedPBWMonomial {n : ℕ} (b : Module.Basis (Fin n) k L)
    (e : Fin n → ℕ) : UniversalEnvelopingAlgebra k L :=
  (List.ofFn fun i : Fin n => UniversalEnvelopingAlgebra.ι k (b i) ^ e i).prod

/-- The exact ordered-product formula, with no commutativity assumption on the algebra. -/
theorem orderedPBWMonomial_eq_orderedProduct {n : ℕ} (b : Module.Basis (Fin n) k L)
    (e : Fin n → ℕ) :
    orderedPBWMonomial b e =
      (List.ofFn fun i : Fin n => UniversalEnvelopingAlgebra.ι k (b i) ^ e i).prod :=
  rfl

/-- A basis with no indices gives the empty product, namely one. -/
@[simp]
theorem orderedPBWMonomial_empty (b : Module.Basis (Fin 0) k L) (e : Fin 0 → ℕ) :
    orderedPBWMonomial b e = 1 := by
  simp [orderedPBWMonomial]

/-- The zero exponent vector gives the unit of the actual quotient algebra. -/
@[simp]
theorem orderedPBWMonomial_zero {n : ℕ} (b : Module.Basis (Fin n) k L) :
    orderedPBWMonomial b (fun _ => 0) = 1 := by
  simp [orderedPBWMonomial, List.ofFn_const]

end Langlands.Algebra.UniversalEnveloping
