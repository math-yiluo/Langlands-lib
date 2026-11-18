import Langlands.AlgebraicGeometry.PointTopology.AffineScheme
import Langlands.GroupScheme.Rational.SplitTorus
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Statement: real points of anisotropic reductive groups are compact and connected -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

/-- **Real points of anisotropic reductive groups** (Borel–Tits 1965, Corollary 9.4 for
`k = ℝ`, and 14.3). Let `G` be a connected reductive group scheme over `ℝ` that is anisotropic,
i.e. of split rank zero. Then the real points `G(ℝ)`, with the evaluation topology (the real
topology), form a compact and connected space.

The affineness binder is needed only to form the topology and follows from reductivity. This
is a statement only; nothing is proved here. -/
def RealAnisotropicCompactConnectedStatement : Prop :=
  ∀ (G : GroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine G.X.left],
    IsConnectedReductive G → IsAnisotropic G →
      CompactSpace (RingPoint ℝ G.X ℝ) ∧ ConnectedSpace (RingPoint ℝ G.X ℝ)

end Langlands.GroupScheme
