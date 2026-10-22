import Langlands.Galois.FiniteField.Frobenius

/-! # Exact target for the Frobenius-normalized finite-field comparison -/

namespace Langlands.Galois.FiniteField

universe u

/-- The complete comparison and finite restriction laws, without assumptions of
procyclicity or a chosen equivalence. Both topological directions are part of
`ContinuousMulEquiv`. -/
def FrobeniusComparison : Prop :=
  ∀ (k : Type u) [Field k] [Finite k],
    (∃ e : Field.absoluteGaloisGroup k ≃ₜ* Langlands.Weil.ProfiniteIntegers,
      e (geometricFrobenius k) =
        Langlands.Weil.frobenius (Multiplicative.ofAdd 1) ∧
      e (arithmeticFrobenius k) =
        Langlands.Weil.frobenius (Multiplicative.ofAdd (-1))) ∧
    (∀ x : AlgebraicClosure k,
      closureAction k (arithmeticFrobenius k) x = x ^ Nat.card k) ∧
    ∀ (L : IntermediateField k (AlgebraicClosure k)) [FiniteDimensional k L],
      finiteRestriction k L (arithmeticFrobenius k) = arithmetic k L ∧
      finiteRestriction k L (geometricFrobenius k) = geometric k L ∧
      (∀ x : L, arithmetic k L x = x ^ Nat.card k) ∧
      orderOf (arithmetic k L) = Module.finrank k L ∧
      orderOf (geometric k L) = Module.finrank k L ∧
      (∀ σ : Gal(L/k), ∃ i : Fin (Module.finrank k L), (arithmetic k L) ^ i.val = σ) ∧
      (∀ σ : Gal(L/k), ∃ i : Fin (Module.finrank k L), (geometric k L) ^ i.val = σ)

end Langlands.Galois.FiniteField
