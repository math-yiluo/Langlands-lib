import Langlands.Representation.Filtration.ConstituentSupportDefinitions

/-! The constituent-support lattice of a multiplicity-free representation. -/

namespace Langlands

universe uK uG uA

/-- In a representation with an actual multiplicity-free composition series,
every invariant subspace has an actual finite simple series, and the
composition-factor support of invariant subspaces, with targets in the ambient
carrier universe, is an order embedding preserving joins, meets, bottom and
top into the subsets of the ambient support. -/
def MultiplicityFreeSubmoduleLatticeStatement : Prop :=
  ∀ (k : Type uK) [Field k] (G : Type uG) [Monoid G] (A : Rep.{uA} k G),
    HasMultiplicityFreeCompositionSeries A →
      let support : Subrepresentation A.ρ → Set (Rep.{uA} k G) :=
        fun S => jordanHolderSupport (Rep.of S.toRepresentation)
      (∀ S : Subrepresentation A.ρ,
        ∃ (n : ℕ) (s : ObjectRepFiltration (Rep.of S.toRepresentation) n),
          s.HasSimpleFactors) ∧
      (∀ S R : Subrepresentation A.ρ, S ≤ R ↔ support S ⊆ support R) ∧
      (∀ S R : Subrepresentation A.ρ,
        support (S ⊔ R) = support S ∪ support R) ∧
      (∀ S R : Subrepresentation A.ρ,
        support (S ⊓ R) = support S ∩ support R) ∧
      support ⊥ = ∅ ∧
      support ⊤ = (jordanHolderSupport A : Set (Rep.{uA} k G))

end Langlands
