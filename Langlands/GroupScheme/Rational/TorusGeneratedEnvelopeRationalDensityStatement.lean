import Langlands.GroupScheme.Rational.TorusGeneratedEnvelope
import Langlands.AlgebraicGeometry.PointTopology.RationalDensityStatement

/-! # Rational density in the fixed closed torus envelope -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over an infinite field, every actual representative of the closed envelope
of all ground-field tori in a smooth connected affine group has dense rational
points in its underlying scheme. -/
def TorusGeneratedEnvelopeRationalDensityStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (D : TorusGeneratedEnvelope G),
    Langlands.AlgebraicGeometry.PointTopology.HasDenseRationalPoints k D.group.X

end Langlands.GroupScheme
