import Langlands.Representation.Filtration.ObjectDefinitions

/-!
# Renard VI.8.5 Lemma: filtrations with distinct central characters split

A representation of a group `G` with a finite filtration whose successive quotients have
pairwise distinct central characters is isomorphic to the direct sum of those quotients.
Central characters are taken on any central subgroup `Z` of `G`, and the direct sum is the
coproduct in the category `Rep k G`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard.AlgebraicFamily

/-- VI.8.5 Lemma: if a central subgroup `Z` of `G` acts on the `i`-th graded quotient of a
finite filtration of `A` through a character `χ i`, and the characters `χ i` are pairwise
distinct, then `A` is isomorphic to the direct sum of the graded quotients. -/
def CentralCharacterSplittingStatement.{uk, uG, uV} : Prop :=
  ∀ (k : Type uk) [Field k] (G : Type uG) [Group G] (Z : Subgroup G),
    Z ≤ Subgroup.center G →
    ∀ (A : Rep.{uV} k G) (n : ℕ) (s : ObjectRepFiltration A n) (χ : Fin n → Z →* kˣ),
      Function.Injective χ →
      (∀ (i : Fin n) (z : Z) (v : s.gradedRepresentation i),
        (s.gradedRepresentation i).ρ (z : G) v = ((χ i z : kˣ) : k) • v) →
      Nonempty (A ≅ ∐ fun i => s.gradedRepresentation i)

end Langlands.Renard.AlgebraicFamily
