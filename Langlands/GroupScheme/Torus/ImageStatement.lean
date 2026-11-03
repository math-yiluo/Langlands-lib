import Langlands.GroupScheme.Torus.Maximal

/-! # Statement: a homomorphism from a torus factors through a closed torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every homomorphism `e : E ⟶ H` from a torus to a smooth affine group scheme over a field
factors as `f ≫ j` through a closed torus `j : Z ⟶ H` (Milne 5.39 and §12.e: the image of `e` is
a closed subgroup of `H` and a quotient of a torus, hence a torus). -/
def TorusImageClosedTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] (E : GroupScheme (Spec (CommRingCat.of k))),
    IsTorus E → ∀ e : E ⟶ H,
      ∃ (Z : CommGroupScheme (Spec (CommRingCat.of k))) (j : Z.toGrp ⟶ H) (f : E ⟶ Z.toGrp),
        IsTorus Z.toGrp ∧ IsClosedSubgroup j ∧ f ≫ j = e

end Langlands.GroupScheme
