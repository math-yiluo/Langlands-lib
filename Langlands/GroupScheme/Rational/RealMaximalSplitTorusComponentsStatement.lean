import Langlands.AlgebraicGeometry.PointTopology.AffineScheme
import Langlands.GroupScheme.Rational.SplitTorus
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Real components are met by every maximal split torus -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

/-- In Matsumoto's theorem (Borel–Tits, 1965, Theorem 14.4), every connected
component of the real points of a smooth connected affine group over `ℝ` meets
any prescribed maximal split torus on real points. -/
def RealMaximalSplitTorusComponentsStatement : Prop :=
  ∀ (G : GroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine G.X.left]
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (S : CommGroupScheme (Spec (CommRingCat.of ℝ))) (i : S.toGrp ⟶ G),
    IsMaximalSplitTorus i →
      ∀ g : RingPoint ℝ G.X ℝ,
        ∃ s : RingPoint ℝ S.X ℝ,
          ConnectedComponents.mk (α := RingPoint ℝ G.X ℝ) (s ≫ i.hom.hom) =
            ConnectedComponents.mk g

end Langlands.GroupScheme
