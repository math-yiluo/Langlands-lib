import Langlands.Representation.Filtration.MultiplicityStatement

/-! Actual composition-factor support and finite multiplicity-free series. -/

namespace Langlands

universe uK uG uA uT

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]

/-- A constituent has positive multiplicity in an actual finite composition
series of `A`; no series or constituent representative is chosen. -/
def HasJordanHolderConstituent (A : Rep.{uA} k G) (τ : Rep.{uT} k G) : Prop :=
  ∃ m : ℕ, HasJordanHolderMultiplicity A τ m ∧ 0 < m

/-- The actual representations in the independently specified target carrier
universe that occur as composition factors of `A`. -/
def jordanHolderSupport (A : Rep.{uA} k G) : Set (Rep.{uT} k G) :=
  {τ | HasJordanHolderConstituent A τ}

/-- Existence of an actual finite simple series whose graded representations
are pairwise inequivalent. The empty series is allowed. -/
def HasMultiplicityFreeCompositionSeries (A : Rep.{uA} k G) : Prop :=
  ∃ (n : ℕ) (s : ObjectRepFiltration A n),
    s.HasSimpleFactors ∧
      ∀ i j : Fin n,
        Nonempty ((s.gradedRepresentation i).ρ.Equiv
          (s.gradedRepresentation j).ρ) → i = j

end Langlands
