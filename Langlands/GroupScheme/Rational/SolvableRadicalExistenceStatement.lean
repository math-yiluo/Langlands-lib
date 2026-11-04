import Langlands.GroupScheme.Rational.LeviSubgroup

/-! # Existence of the ground-field solvable radical -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every smooth connected affine group scheme over a field has a represented
ground-field solvable radical. This declaration is a proposition target. -/
def SolvableRadicalExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    ∃ (R : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ G),
      IsSolvableRadical r

end Langlands.GroupScheme
