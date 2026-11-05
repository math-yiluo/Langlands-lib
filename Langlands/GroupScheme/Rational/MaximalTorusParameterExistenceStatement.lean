import Langlands.GroupScheme.Rational.MaximalTorusParameter

/-! # Statement: existence of the actual maximal-torus parameter scheme -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every maximal torus in a smooth connected affine group over any field admits
an actual parameter scheme and projection with the full geometric, all-test fiber,
and ground-field torus compatibility properties. -/
def MaximalTorusParameterExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T₀ : CommGroupScheme (Spec (CommRingCat.of k))) (j₀ : T₀.toGrp ⟶ G),
    IsMaximalTorus j₀ →
      ∃ (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q),
        IsMaximalTorusParameter j₀ q

end Langlands.GroupScheme
