import Langlands.GroupScheme.Rational.TorusGeneratedEnvelope

/-! # Compatibility of the fixed closed torus envelope with algebraic closure -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over every infinite field, base change to the algebraic closure carries the
closed envelope of all ground-field tori of a smooth connected affine group onto
the closed envelope of all tori of the base-changed group, on every test scheme. -/
def TorusGeneratedEnvelopeAlgebraicClosureInfiniteStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    (closedTorusEnvelope G).baseChange (toAlgebraicClosure k) =
      closedTorusEnvelope ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G)

/-- Over every finite field, base change to the algebraic closure carries the
closed envelope of all ground-field tori of a smooth connected affine group onto
the closed envelope of all tori of the base-changed group, on every test scheme. -/
def TorusGeneratedEnvelopeAlgebraicClosureFiniteStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    (closedTorusEnvelope G).baseChange (toAlgebraicClosure k) =
      closedTorusEnvelope ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G)

end Langlands.GroupScheme
