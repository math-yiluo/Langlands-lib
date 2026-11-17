import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceDimensionTopologyStatement

/-! # The actual smooth dimension decomposition is a homeomorphism on rational points -/

noncomputable section

universe u

open _root_.AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology (IsHenselianValuedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- **The dimension decomposition is a homeomorphism.** Each dimension piece is quasi-separated
and smooth, hence locally of finite type, and its actual inclusion is an open immersion, so
`isOpenEmbedding_ringPointsMap` makes the inclusion-induced point map an open embedding. The
inverse of `SmoothDimensionPieces.fieldPointEquiv hX` is this map summand by summand; it is
therefore continuous and open for the Sigma topology, and the equivalence is a homeomorphism. -/
theorem smoothSourceDimensionTopology : SmoothSourceDimensionTopologyStatement.{u} := by
  intro K _ hK X hX hqs
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  let : ∀ n : ℕ, TopologicalSpace (RingPoints K (SmoothDimensionPieces.space hX n) K) :=
    fun n => etaleChartTopology K (SmoothDimensionPieces.space hX n)
  have hXq : IsQuasiSeparatedLocallyFiniteType K X := ⟨hqs, hX.locallyOfFiniteType⟩
  have hemb : ∀ n : ℕ, IsOpenEmbedding
      (RingPoints.map (A := K) (SmoothDimensionPieces.inclusion hX n)) := fun n =>
    isOpenEmbedding_ringPointsMap hK
      ⟨SmoothDimensionPieces.space_isQuasiSeparated hX hqs n,
        (SmoothDimensionPieces.space_smoothOverBase hX n).locallyOfFiniteType⟩
      hXq (SmoothDimensionPieces.inclusion hX n)
      (SmoothDimensionPieces.inclusion_isOpenImmersion hX n)
  let e := SmoothDimensionPieces.fieldPointEquiv (L := K) hX
  have hcont : Continuous e.symm := continuous_sigma fun n => (hemb n).continuous
  have hopen : IsOpenMap e.symm := isOpenMap_sigma.2 fun n => (hemb n).isOpenMap
  exact (e.symm.toHomeomorphOfContinuousOpen hcont hopen).symm.isHomeomorph

end Langlands.AlgebraicGeometry.AlgebraicSpace
