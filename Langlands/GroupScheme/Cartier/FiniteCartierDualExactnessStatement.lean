import Langlands.Geometry.FormalGroup.ScalarTorsionSchemeExactness
import Langlands.GroupScheme.Cartier.FiniteDualSchemes

/-! # Exactness of finite locally free Cartier duality over an affine base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Cartier

open FiniteDual

/-- Cartier duality sends every short exact sequence of finite locally free commutative
 group schemes to the reversed short exact sequence on affine fppf tests. -/
def FiniteCartierDualExactnessStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (G H J : CommGroupScheme (Spec R))
    [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    [IsFinite H.X.hom] [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom]
    [IsFinite J.X.hom] [Flat J.X.hom] [LocallyOfFinitePresentation J.X.hom]
    (i : G ⟶ H) (q : H ⟶ J),
    Langlands.CommGroupScheme.AffineFppfShortExact i q →
      Langlands.CommGroupScheme.AffineFppfShortExact (schemeDualMap q) (schemeDualMap i)

end Langlands.GroupScheme.Cartier
