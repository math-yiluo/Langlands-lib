import Langlands.Representation.Filtration.MultiplicityStatement

/-! Actual finite-series and factor-count transport interfaces. -/

namespace Langlands

universe uK uG uH uA uB uT uU

/-- Pullback along an actual group equivalence preserves the supplied chain
of vector subspaces, its graded factors, simplicity and exact factor count. -/
def GroupEquivFiltrationMultiplicityTransportStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Group G]
    (H : Type uH) [Group H] (e : H ≃* G)
    (A : Rep.{uA} k G) (τ : Rep.{uT} k G)
    (n : ℕ) (s : ObjectRepFiltration A n),
    ∃ t : ObjectRepFiltration (Rep.of (A.ρ.comp e.toMonoidHom)) n,
      (∀ i : Fin (n + 1),
        (t.subrepresentation i).toSubmodule = (s.subrepresentation i).toSubmodule) ∧
      (s.HasSimpleFactors ↔ t.HasSimpleFactors) ∧
      (∀ i : Fin n, Nonempty (Representation.Equiv
        ((s.gradedRepresentation i).ρ.comp e.toMonoidHom)
        (t.gradedRepresentation i).ρ)) ∧
      t.factorMultiplicity (Rep.of (τ.ρ.comp e.toMonoidHom)) =
        s.factorMultiplicity τ

/-- Actual ambient and constituent equivalences preserve the length and exact
count in every supplied composition series, with indexwise graded equivalences. -/
def EquivCompositionSeriesMultiplicityTransportStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (A : Rep.{uA} k G) (B : Rep.{uB} k G)
    (τ : Rep.{uT} k G) (υ : Rep.{uU} k G)
    (_φ : A.ρ.Equiv B.ρ) (_ψ : τ.ρ.Equiv υ.ρ)
    (n : ℕ) (s : ObjectRepFiltration A n),
    s.HasSimpleFactors →
      ∃ t : ObjectRepFiltration B n, t.HasSimpleFactors ∧
        (∀ i : Fin n, Nonempty ((s.gradedRepresentation i).ρ.Equiv
          (t.gradedRepresentation i).ρ)) ∧
        t.factorMultiplicity υ = s.factorMultiplicity τ

/-- The same multiplicity predicate in both directions under actual group
pullback; its witnesses must come from actual finite composition series. -/
def GroupEquivJordanHolderMultiplicityTransportStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Group G]
    (H : Type uH) [Group H] (e : H ≃* G)
    (A : Rep.{uA} k G) (τ : Rep.{uT} k G) (m : ℕ),
    HasJordanHolderMultiplicity A τ m ↔
      HasJordanHolderMultiplicity (Rep.of (A.ρ.comp e.toMonoidHom))
        (Rep.of (τ.ρ.comp e.toMonoidHom)) m

/-- The same multiplicity predicate in both directions under actual ambient
and constituent representation equivalences, with four carrier universes. -/
def EquivJordanHolderMultiplicityTransportStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G]
    (A : Rep.{uA} k G) (B : Rep.{uB} k G)
    (τ : Rep.{uT} k G) (υ : Rep.{uU} k G)
    (_φ : A.ρ.Equiv B.ρ) (_ψ : τ.ρ.Equiv υ.ρ) (m : ℕ),
    HasJordanHolderMultiplicity A τ m ↔ HasJordanHolderMultiplicity B υ m

/-- The two actual-series constructions and their multiplicity consequences,
with independent field, group and representation-carrier universes. -/
def MultiplicityTransportStatement : Prop :=
  GroupEquivFiltrationMultiplicityTransportStatement.{uK, uG, uH, uA, uT} ∧
    EquivCompositionSeriesMultiplicityTransportStatement.{uK, uG, uA, uB, uT, uU} ∧
    GroupEquivJordanHolderMultiplicityTransportStatement.{uK, uG, uH, uA, uT} ∧
    EquivJordanHolderMultiplicityTransportStatement.{uK, uG, uA, uB, uT, uU}

end Langlands
