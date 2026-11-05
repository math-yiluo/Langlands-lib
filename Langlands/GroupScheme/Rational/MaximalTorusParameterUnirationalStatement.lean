import Langlands.GroupScheme.Rational.MaximalTorusParameter
import Langlands.AlgebraicGeometry.PointTopology.UnirationalDensity

/-! # Unirationality of the same actual maximal-torus parameter scheme -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every actual maximal-torus parameter scheme with the stated quotient
properties is unirational over its ground field. -/
def MaximalTorusParameterUnirationalStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T₀ : CommGroupScheme (Spec (CommRingCat.of k))) (j₀ : T₀.toGrp ⟶ G),
    IsMaximalTorus j₀ →
      ∀ (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q),
        IsMaximalTorusParameter j₀ q →
          Langlands.AlgebraicGeometry.PointTopology.IsUnirational k Q

end Langlands.GroupScheme
