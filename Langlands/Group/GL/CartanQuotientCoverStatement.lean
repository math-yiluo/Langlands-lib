import Langlands.Group.GL.CartanQuotientDefinitions

/-!
# Normalized Cartan coverage of the actual central quotient

The unique object is the normalized exponent tuple. These proposition definitions
assert no uniqueness of integral factors and no covering by arbitrary subgroup cells.
-/

namespace Langlands.GeneralLinear.CartanQuotient

universe uF

/-- Every point of the actual central quotient belongs to a unique normalized
Cartan cell at positive rank. -/
def CartanQuotientCoverStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ), 0 < n → ∀ x : centralQuotient F n,
      ∃! lam : Fin n → ℤ, Normalized lam ∧ x ∈ cell T lam

/-- Distinct normalized exponent tuples have disjoint cells in the actual
central quotient. -/
def CartanQuotientDisjointStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ), 0 < n → ∀ lam mu : Fin n → ℤ,
      Normalized lam → Normalized mu → lam ≠ mu →
        Disjoint (cell T lam) (cell T mu)

end Langlands.GeneralLinear.CartanQuotient
