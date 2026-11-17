import Langlands.AlgebraicGeometry.PointTopology.AffineScheme
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Statement: real approximation over `ℚ` (Milne 25.70) -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

/-- **Real approximation** (Milne, *Algebraic Groups*, Theorem 25.70). Let `G` be a smooth
connected affine group scheme over `ℚ`. Then the rational points `G(ℚ)`, mapped into the real
points `G(ℝ)` by change of rings along `ℚ → ℝ`, are dense for the evaluation topology on
`G(ℝ)`, which is the real topology.

This is a statement only; nothing is proved here. -/
def RealApproximationStatement : Prop :=
  ∀ (G : GroupScheme (Spec (CommRingCat.of ℚ))) [IsAffine G.X.left],
    Smooth G.X.hom → ConnectedSpace G.X.left →
      DenseRange (fun p : RingPoint ℚ G.X ℚ => p.changeRing (Algebra.ofId ℚ ℝ))

end Langlands.GroupScheme
