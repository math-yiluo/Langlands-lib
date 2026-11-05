import Langlands.GroupScheme.Rational.AnisotropicCompactnessStatement

/-! # Compact rational points force anisotropy: affine target -/

universe u

open AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

/-- The compact-to-anisotropic implication with only the needed affineness hypothesis. -/
def CompactPointsAnisotropyStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left],
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsCompact (Set.univ : Set (rationalPoints G)) → IsAnisotropic G

end Langlands.GroupScheme
