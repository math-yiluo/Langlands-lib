import Langlands.Representation.Classification.CanonicalConstituents

/-!
# Strong irreducible constituents from lattice extrema

This internal algebraic interface connects uniqueness of an atom or coatom of
the actual subrepresentation lattice to the canonical strong socle or head.
It does not assert that either extremum exists for an arbitrary representation.
-/

namespace Langlands.Classification

universe uG uV

/-- Unique atoms and coatoms characterize the canonical strong irreducible
socle and head. The uniqueness concerns actual subrepresentations. -/
def StrongConstituentExtremaStatement : Prop :=
  ∀ (G : Type uG) [Group G] (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V),
    ((∃! S : Subrepresentation ρ, IsCoatom S) ↔
      IsIrreducibleHead ρ (head ρ)) ∧
    ((∃! S : Subrepresentation ρ, IsAtom S) ↔
      IsIrreducibleSocle ρ (socleRepresentation ρ))

end Langlands.Classification
