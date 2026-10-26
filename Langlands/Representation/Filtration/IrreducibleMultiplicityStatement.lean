import Langlands.Representation.Filtration.MultiplicityStatement

/-! Actual one-factor composition series and counts for an irreducible object. -/

namespace Langlands

universe uK uG uA uT

/-- An irreducible object has an actual one-step composition series whose only
quotient is equivalent to the original representation. -/
def IrreducibleCompositionSeriesStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (A : Rep.{uA} k G), Representation.IsIrreducible A.ρ →
      ∃ s : ObjectRepFiltration A 1, s.HasSimpleFactors ∧
        Nonempty ((s.gradedRepresentation 0).ρ.Equiv A.ρ)

/-- The count of any specified object in an irreducible object is exactly one
when the objects are equivalent, and exactly zero otherwise. -/
def IrreducibleJordanHolderMultiplicityStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (A : Rep.{uA} k G) (τ : Rep.{uT} k G),
    Representation.IsIrreducible A.ρ → ∀ m : ℕ,
      HasJordanHolderMultiplicity A τ m ↔
        (Nonempty (A.ρ.Equiv τ.ρ) ∧ m = 1) ∨
        (¬ Nonempty (A.ρ.Equiv τ.ρ) ∧ m = 0)

/-- The actual one-factor series and its exact constituent-count consequences,
with independent field, monoid and both carrier universes. -/
def IrreducibleMultiplicityStatement : Prop :=
  IrreducibleCompositionSeriesStatement.{uK, uG, uA} ∧
    IrreducibleJordanHolderMultiplicityStatement.{uK, uG, uA, uT}

end Langlands
