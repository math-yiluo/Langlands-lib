import Langlands.Representation.Filtration.LengthCriterionProof

/-! Lifting an actual composition series of a successive quotient representation
to a covering chain of invariant subspaces between its two endpoints. -/

namespace Langlands

universe uK uG uV

/-- For invariant subspaces `S ≤ T` of an actual representation, every actual
composition series of the successive quotient representation of `T` by `S` lifts
to a chain of covering steps from `S` to `T`. An index bijection matches every
step of the chain with one factor occurrence of the series, through an actual
representation equivalence of the step's successive quotient with that factor.
This proposition states the existence claim only. -/
def ActualQuotientSeriesLiftStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G] (A : Rep.{uV} k G)
    (S T : Subrepresentation A.ρ), S ≤ T →
    ∀ (n : ℕ)
      (f : ObjectRepFiltration (Rep.of (LengthCriterionProof.quotientRep S T)) n),
      f.HasSimpleFactors →
        ∃ c : RelSeries {(X, Y) : Subrepresentation A.ρ × Subrepresentation A.ρ | X ⋖ Y},
          c.head = S ∧ c.last = T ∧
            ∃ e : Fin c.length ≃ Fin n,
              ∀ i : Fin c.length,
                Nonempty (Representation.Equiv
                  (LengthCriterionProof.quotientRep (c i.castSucc) (c i.succ))
                  (f.gradedRepresentation (e i)).ρ)

end Langlands
