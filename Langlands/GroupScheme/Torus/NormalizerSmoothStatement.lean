import Langlands.GroupScheme.Rational.TorusNormalizerStatement

/-! # Statement: smooth closed normalizers of arbitrary field tori

The all-test normalizer of a closed torus in a smooth affine group scheme over a
field has a smooth closed representative (Milne, Algebraic Groups, Proposition
1.83 and Corollary 13.10).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every closed torus in a smooth affine group scheme over a field has an all-test
normalizer represented by a smooth closed subgroup (Milne 1.83 and 13.10).
The torus need not be split or maximal, and the ambient group need not be connected
or reductive. -/
def TorusNormalizerSmoothClosedStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G),
    IsTorus T.toGrp → IsClosedSubgroup i →
      (torusNormalizer i).HasSmoothClosedRepresentative

end Langlands.GroupScheme
