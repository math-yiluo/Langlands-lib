import Langlands.Representation.Filtration.ObjectDefinitions

/-! Comparison, transport and transitivity for actual Jordan–Hölder series. -/

namespace Langlands

/-- Any two supplied composition series of one actual representation have
their graded quotients matched by a bijection of indices, each matched pair
being equivalent as representations. This proposition proves nothing. -/
def JordanHolderSeriesComparisonStatement.{uK, uG, uA} : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (A : Rep.{uA} k G) (n m : ℕ)
    (s : ObjectRepFiltration A n) (t : ObjectRepFiltration A m),
    s.HasSimpleFactors → t.HasSimpleFactors →
      ∃ e : Fin n ≃ Fin m, ∀ i : Fin n,
        Nonempty ((s.gradedRepresentation i).ρ.Equiv
          (t.gradedRepresentation (e i)).ρ)

/-- An equivalence `A ≃ B` carries a supplied composition series of `A` to a
composition series of `B` of the same length whose graded quotients are
equivalent to those of the given series at the same index. -/
def JordanHolderSeriesTransportStatement.{uK, uG, uA, uB} : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (A : Rep.{uA} k G) (B : Rep.{uB} k G),
    A.ρ.Equiv B.ρ → ∀ (n : ℕ) (s : ObjectRepFiltration A n),
    s.HasSimpleFactors →
      ∃ t : ObjectRepFiltration B n, t.HasSimpleFactors ∧
        ∀ i : Fin n,
          Nonempty ((s.gradedRepresentation i).ρ.Equiv
            (t.gradedRepresentation i).ρ)

/-- Matching of actual composition factors with multiplicities is transitive.
The two witnesses may use different composition series of the middle
representation `B`. -/
def HaveSameJordanHolderFactorsTransStatement.{uK, uG, uA, uB, uC} : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (A : Rep.{uA} k G) (B : Rep.{uB} k G) (C : Rep.{uC} k G),
    HaveSameJordanHolderFactors A B → HaveSameJordanHolderFactors B C →
      HaveSameJordanHolderFactors A C

/-- The three clauses together, with independent universes for the field,
the monoid and the three representation carriers. This is the single target
of a later proof; it is a conjunction of propositions, not a proof. -/
def JordanHolderSeriesStatement.{uK, uG, uA, uB, uC} : Prop :=
  JordanHolderSeriesComparisonStatement.{uK, uG, uA} ∧
    JordanHolderSeriesTransportStatement.{uK, uG, uA, uB} ∧
      HaveSameJordanHolderFactorsTransStatement.{uK, uG, uA, uB, uC}

end Langlands
