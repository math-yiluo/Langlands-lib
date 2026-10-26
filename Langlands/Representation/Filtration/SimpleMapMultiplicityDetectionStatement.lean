import Langlands.Representation.Filtration.MultiplicityStatement

/-! Positive actual-series multiplicity detected by a nonzero simple map. -/

namespace Langlands

universe uK uG uA uB uT

/-- A subrepresentation of an object with an actual finite simple series has
a positive bounded count for a simple test object admitting a nonzero map
to or from that subrepresentation. -/
def JordanHolderSubobjectSimpleMapDetectionStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (A : Rep.{uA} k G) (B : Rep.{uB} k G) (τ : Rep.{uT} k G),
    Representation.IsIrreducible τ.ρ →
    ∀ (i : B.ρ.IntertwiningMap A.ρ), Function.Injective i →
    ∀ M : ℕ, HasJordanHolderMultiplicity A τ M →
    ((∃ f : τ.ρ.IntertwiningMap B.ρ, f ≠ 0) ∨
      (∃ f : B.ρ.IntertwiningMap τ.ρ, f ≠ 0)) →
    ∃ m : ℕ, HasJordanHolderMultiplicity B τ m ∧ 0 < m ∧ m ≤ M

/-- A quotient of an object with an actual finite simple series has a
positive bounded count for a simple test object admitting a nonzero map
to or from that quotient. -/
def JordanHolderQuotientSimpleMapDetectionStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (A : Rep.{uA} k G) (B : Rep.{uB} k G) (τ : Rep.{uT} k G),
    Representation.IsIrreducible τ.ρ →
    ∀ (q : A.ρ.IntertwiningMap B.ρ), Function.Surjective q →
    ∀ M : ℕ, HasJordanHolderMultiplicity A τ M →
    ((∃ f : τ.ρ.IntertwiningMap B.ρ, f ≠ 0) ∨
      (∃ f : B.ρ.IntertwiningMap τ.ρ, f ≠ 0)) →
    ∃ m : ℕ, HasJordanHolderMultiplicity B τ m ∧ 0 < m ∧ m ≤ M

/-- Both simple-map detection clauses, with independent field, monoid,
ambient, subobject or quotient, and test universes. -/
def JordanHolderSimpleMapDetectionStatement : Prop :=
  JordanHolderSubobjectSimpleMapDetectionStatement.{uK, uG, uA, uB, uT} ∧
    JordanHolderQuotientSimpleMapDetectionStatement.{uK, uG, uA, uB, uT}

end Langlands
