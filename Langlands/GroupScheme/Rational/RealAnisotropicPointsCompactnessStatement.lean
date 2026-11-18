import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Rational.PointTopology

/-! # Compact real points of an anisotropic semisimple group -/

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

/-- An anisotropic semisimple group over the real numbers has compact rational
points in the canonical evaluation topology. This is a statement target. -/
def RealAnisotropicPointsCompactnessStatement : Prop :=
  ∀ (G : GroupScheme (Spec (CommRingCat.of ℝ))) (hG : IsSemisimple G),
    letI : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology ℝ G.X
    IsAnisotropic G → IsCompact (Set.univ : Set (rationalPoints G))

end Langlands.GroupScheme
