import Langlands.GroupScheme.Rational.TorusGeneratedEnvelope

/-! # Smooth connected representability of the closed torus envelope -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over every field, the fixed closed envelope of all ground-field tori in a
smooth connected affine group has a smooth connected actual representative. -/
def TorusGeneratedEnvelopeExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    ∃ D : TorusGeneratedEnvelope G,
      Smooth D.group.X.hom ∧ ConnectedSpace D.group.X.left

end Langlands.GroupScheme
