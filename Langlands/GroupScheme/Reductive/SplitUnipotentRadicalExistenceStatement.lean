import Langlands.GroupScheme.Reductive.UnipotentRadical

/-! # Existence of the split ground-field unipotent radical -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every smooth connected affine group scheme over a field has a represented
split ground-field unipotent radical. This declaration is a proposition target. -/
def SplitUnipotentRadicalExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    ∃ (V : GroupScheme (Spec (CommRingCat.of k))) (j : V ⟶ G),
      IsSplitUnipotentRadical j

end Langlands.GroupScheme
