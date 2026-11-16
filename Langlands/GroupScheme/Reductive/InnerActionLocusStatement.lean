import Langlands.GroupScheme.Reductive.ConnectedActionInnerStatement
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Statement: the clopen inner part of an action on a reductive group -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The inverse image of the adjoint subgroup in the automorphism group is an
open and closed subgroup of the acting group, universal for inner restrictions.
This is a consequence of Conrad, Theorem 7.1.9(1), without a connectedness
hypothesis on the acting group. -/
def ReductiveInnerActionLocusStatement : Prop :=
  ∀ (S : Scheme.{u}) (G H : GroupScheme S), IsReductive G →
    ∀ (Gad : GroupScheme S) (p : G ⟶ Gad),
      RelativeRoot.IsFppfQuotient (center G) p →
    ∀ c : AutomorphicAction Gad G,
      c.restrict p = AutomorphicAction.conjugation (𝟙 G) →
    ∀ a : AutomorphicAction H G,
      ∃ (K : GroupScheme S) (j : K ⟶ H) (φ : K ⟶ Gad),
        IsOpenImmersion j.hom.hom.left ∧ IsClosedImmersion j.hom.hom.left ∧
        c.restrict φ = a.restrict j ∧
        ∀ (L : GroupScheme S) (h : L ⟶ H) (x : L ⟶ Gad),
          c.restrict x = a.restrict h →
          ∃! f : L ⟶ K, f ≫ j = h ∧ f ≫ φ = x

end Langlands.GroupScheme
