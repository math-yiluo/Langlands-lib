import Langlands.GroupScheme.Rational.RealApproximationStatement

/-! # Reduction of real approximation to connected reductive groups -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

/-- Real approximation restricted to connected reductive groups over the rationals. -/
def ReductiveRealApproximationStatement : Prop :=
  ∀ (G : GroupScheme (Spec (CommRingCat.of ℚ))) [IsAffine G.X.left],
    IsConnectedReductive G →
      DenseRange (fun p : RingPoint ℚ G.X ℚ => p.changeRing (Algebra.ofId ℚ ℝ))

/-- Characteristic-zero Levi decomposition reduces real approximation to the
connected reductive case. -/
def RealApproximationReductiveReductionStatement : Prop :=
  ReductiveRealApproximationStatement → RealApproximationStatement

end Langlands.GroupScheme
