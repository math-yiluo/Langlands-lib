import Langlands.GroupScheme.Rational.TorusGeneratedEnvelope

/-! # Statement: torus envelope normality for solvable groups over a finite field -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over a finite field, the closed envelope of all ground-field tori of a smooth connected
affine solvable group is normal on every test scheme. -/
def FiniteFieldSolvableEnvelopeNormalityStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    IsSolvableGroupScheme G → (closedTorusEnvelope G).IsNormal

end Langlands.GroupScheme
