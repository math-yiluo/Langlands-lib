import Langlands.GroupScheme.Torus.Maximal

/-! # Statement: maximal tori over the original field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every smooth affine group scheme over a field has a maximal torus over that
field (the rational existence input to Milne, Corollary 17.83). -/
def MaximalTorusExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom],
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalTorus i

end Langlands.GroupScheme
