import Langlands.AlgebraicGeometry.PointTopology.AffineScheme
import Langlands.GroupScheme.SimplyConnected.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Statement: connected components of real points (Milne 25.54, 25.55) -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

/-- **Real points of reductive groups** (Milne, *Algebraic Groups*, Theorem 25.54 (Cartan)
and Corollary 25.55). Let `G` be an affine group scheme over `ℝ`, and give its real points
`G(ℝ)` the evaluation topology, which is the real topology.
1. If `G` is semisimple and simply connected, then `G(ℝ)` is connected.
2. If `G` is connected reductive, then `G(ℝ)` has only finitely many connected components.

The affineness binder is the source's convention and follows from either hypothesis. This is a
statement only; nothing is proved here. -/
def RealPointComponentsStatement : Prop :=
  ∀ (G : GroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine G.X.left],
    (IsSimplyConnected G → ConnectedSpace (RingPoint ℝ G.X ℝ)) ∧
      (IsConnectedReductive G → Finite (ConnectedComponents (RingPoint ℝ G.X ℝ)))

end Langlands.GroupScheme
