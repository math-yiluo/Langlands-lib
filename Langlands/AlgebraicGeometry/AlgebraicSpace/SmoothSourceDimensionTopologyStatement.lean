import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceDimensionFieldPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopologyFunctorial
import Mathlib.Topology.Constructions

/-! # Rational-point topology of the actual smooth dimension decomposition -/

universe u

open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (IsHenselianValuedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The actual section equivalence for all natural-number dimension pieces is a
homeomorphism for the étale-chart topologies and their topological disjoint union.
This is a derived bridge for the varying-dimension clause of Conrad Proposition 5.4. -/
def SmoothSourceDimensionTopologyStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K], IsHenselianValuedField K →
    ∀ (X : AlgebraicSpace (Spec (CommRingCat.of K))) (hX : SmoothOverBase X),
      IsQuasiSeparated X →
        letI := etaleChartTopology K X
        letI : ∀ n : ℕ, TopologicalSpace (RingPoints K (SmoothDimensionPieces.space hX n) K) :=
          fun n => etaleChartTopology K (SmoothDimensionPieces.space hX n)
        IsHomeomorph (fun x : RingPoints K X K =>
          SmoothDimensionPieces.fieldPointEquiv hX x)

end Langlands.AlgebraicGeometry.AlgebraicSpace
