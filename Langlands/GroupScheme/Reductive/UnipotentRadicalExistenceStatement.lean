import Langlands.GroupScheme.Reductive.UnipotentRadical

/-! # Existence of the ground-field unipotent radical -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every smooth connected affine group scheme over a field has a represented
ground-field unipotent radical. This declaration is a proposition target. -/
def UnipotentRadicalExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G),
      IsUnipotentRadical i

end Langlands.GroupScheme
