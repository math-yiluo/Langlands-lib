import Langlands.GroupScheme.Rational.TorusGeneratedEnvelope

/-! # Normality of the fixed closed torus envelope -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The closed envelope of all ground-field tori in a smooth connected affine
 group is normal on every relative test scheme. -/
def TorusGeneratedEnvelopeNormalityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (D : TorusGeneratedEnvelope G),
    (SubgroupFunctor.range D.inclusion).IsNormal

end Langlands.GroupScheme
