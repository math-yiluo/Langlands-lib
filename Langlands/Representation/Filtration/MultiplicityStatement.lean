import Langlands.Representation.Filtration.ObjectDefinitions

/-! Jordan–Hölder multiplicities of a single constituent. -/

namespace Langlands

universe uR uG uV uW

section Field

variable {k : Type uR} [Field k] {G : Type uG} [Monoid G]

/-- The number of graded quotients of the filtration `s` that are equivalent
to `τ`. It is a count for this one filtration; no series is chosen. -/
noncomputable def ObjectRepFiltration.factorMultiplicity {A : Rep.{uV} k G} {n : ℕ}
    (s : ObjectRepFiltration A n) (τ : Rep.{uW} k G) : ℕ :=
  Nat.card {i : Fin n // Nonempty ((s.gradedRepresentation i).ρ.Equiv τ.ρ)}

/-- `A` has an actual composition series in which exactly `m` composition
factors are equivalent to `τ`. This is Silberger's `[τ, A] = m`. -/
def HasJordanHolderMultiplicity (A : Rep.{uV} k G) (τ : Rep.{uW} k G) (m : ℕ) : Prop :=
  ∃ (n : ℕ) (s : ObjectRepFiltration A n),
    s.HasSimpleFactors ∧ s.factorMultiplicity τ = m

end Field

/-- Jordan–Hölder independence of a single multiplicity: any two actual
composition series of one representation contain the same number of factors
equivalent to a given representation. -/
def JordanHolderMultiplicityIndependenceStatement : Prop :=
  ∀ (k : Type uR) [Field k] (G : Type uG) [Monoid G]
    (A : Rep.{uV} k G) (τ : Rep.{uW} k G) (n n' : ℕ)
    (s : ObjectRepFiltration A n) (t : ObjectRepFiltration A n'),
    s.HasSimpleFactors → t.HasSimpleFactors →
      s.factorMultiplicity τ = t.factorMultiplicity τ

end Langlands
