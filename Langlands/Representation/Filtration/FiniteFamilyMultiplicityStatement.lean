import Langlands.Representation.Filtration.MultiplicityStatement

/-! Exact length and multiplicity from a finite family of actual factors. -/

namespace Langlands

universe uK uG uI uA uB uT

/-- A supplied filtration indexed by a finite family of irreducible
representations has the family's cardinality as its length, and its
Jordan–Hölder multiplicities count the family indices, including repetitions. -/
def FiniteFamilyFiltrationMultiplicityStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (I : Type uI) [Finite I] (A : Rep.{uA} k G) (family : I → Rep.{uB} k G),
    (∀ i, Representation.IsIrreducible (family i).ρ) →
    ∀ (r : ℕ) (e : Fin r ≃ I) (s : ObjectRepFiltration A r),
      (∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv (family (e i)).ρ)) →
        HasCompositionSeriesLength A (Nat.card I) ∧
        ∀ (τ : Rep.{uT} k G) (m : ℕ),
          HasJordanHolderMultiplicity A τ m ↔
            m = Nat.card {i : I // Nonempty ((family i).ρ.Equiv τ.ρ)}

end Langlands
