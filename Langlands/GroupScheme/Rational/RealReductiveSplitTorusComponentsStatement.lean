import Langlands.AlgebraicGeometry.PointTopology.AffineScheme
import Langlands.GroupScheme.Rational.SplitTorus
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Statement: a maximal split torus meets every real component of a reductive group -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

/-- **Matsumoto's theorem for reductive groups** (Borel–Tits 1965, Theorem 14.4, for connected
reductive `G`). Let `G` be a connected reductive group scheme over `ℝ` and `i : S → G` a maximal
split torus. Then every connected component of the real points `G(ℝ)`, with the evaluation
topology, contains the image `s ≫ i` of a real point `s` of `S`; that is,
`G(ℝ) = G(ℝ)⁰ · S(ℝ)`.

The affineness binder is needed only to form the topology and follows from reductivity. This
is a statement only; nothing is proved here. -/
def RealReductiveSplitTorusComponentsStatement : Prop :=
  ∀ (G : GroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine G.X.left],
    IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of ℝ))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
      ∀ g : RingPoint ℝ G.X ℝ, ∃ s : RingPoint ℝ S.X ℝ,
        ConnectedComponents.mk (α := RingPoint ℝ G.X ℝ) (s ≫ i.hom.hom) =
          ConnectedComponents.mk g

end Langlands.GroupScheme
