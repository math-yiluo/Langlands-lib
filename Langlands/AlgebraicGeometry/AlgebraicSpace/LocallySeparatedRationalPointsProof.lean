import Langlands.AlgebraicGeometry.AlgebraicSpace.LocallySeparatedRationalPointsStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTotallyDisconnected
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# Proof that rational points of locally separated spaces are locally Hausdorff

Over a henselian valued field `K`, every rational point `x` of a quasi-separated, locally
separated algebraic space `X` locally of finite type is the image of a rational point `u` of
an affine étale chart `U`. Local separatedness makes the chart map injective on an open
neighbourhood `N` of `u`; being continuous and open, it maps `N` homeomorphically onto an
open neighbourhood `W` of `x`. The rational points of the affine scheme `U` embed into a
power of `K`, so `N`, and hence `W`, is Hausdorff, and totally disconnected when the norm of
`K` is ultrametric. Local compactness of `W` follows from that of `X(K)`.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint schemePointTopology IsHenselianValuedField AlgPoint affineSchemePointHomeomorph)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {K : Type u} [NontriviallyNormedField K]

/-- The rational points of an affine `K`-scheme are Hausdorff for the scheme point
topology. -/
theorem t2Space_schemePointTopology_of_isAffine (U : Over (Spec (CommRingCat.of K)))
    [IsAffine U.left] : @T2Space _ (schemePointTopology K U K) := by
  rw [PointTopology.schemePointTopology_eq_affine]
  exact (affineSchemePointHomeomorph K U K).isEmbedding.t2Space

/-- Over a field with ultrametric norm, the rational points of an affine `K`-scheme are
totally disconnected for the scheme point topology. -/
theorem totallyDisconnectedSpace_schemePointTopology_of_isAffine [IsUltrametricDist K]
    (U : Over (Spec (CommRingCat.of K))) [IsAffine U.left] :
    @TotallyDisconnectedSpace _ (schemePointTopology K U K) := by
  rw [PointTopology.schemePointTopology_eq_affine]
  have : TotallyDisconnectedSpace (AlgPoint K (PointTopology.AffineCoordinateRing K U) K) :=
    AlgPoint.isEmbedding_evaluation.isTotallyDisconnected_range.mp
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  exact (affineSchemePointHomeomorph K U K).symm.totallyDisconnectedSpace

/-- **Rational points of locally separated spaces are locally Hausdorff**: over a henselian
valued field, every rational point of a quasi-separated, locally separated algebraic space
locally of finite type has an open neighbourhood that is Hausdorff, locally compact if the
field is, and totally disconnected if its norm is ultrametric. -/
theorem locallySeparatedRationalPoints : LocallySeparatedRationalPointsStatement.{u} := by
  intro K _ hK X hX
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  intro x
  obtain ⟨c, u, hc, rfl⟩ := exists_affine_chart_pointMap_eq hX.1.1 hX.1.2 x
  let : TopologicalSpace (RingPoint K c.scheme K) := schemePointTopology K c.scheme K
  obtain ⟨N, hN, huN, hinj⟩ :=
    exists_isOpen_injOn_schemePointsMap (AlgebraicSpace.hom c.hom) hX.2 c.isEtale u
  have hinj' : Set.InjOn c.pointMap N := hinj
  let g : N → RingPoints K X K := fun p => c.pointMap p
  have hg : IsOpenEmbedding g :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap
      (c.continuous_pointMap.comp continuous_subtype_val)
      (fun p q h => Subtype.ext (hinj' p.2 q.2 h))
      ((c.isOpenMap_pointMap hK).domRestrict hN)
  let e : N ≃ₜ Set.range g := hg.isEmbedding.toHomeomorph
  have : T2Space (RingPoint K c.scheme K) := t2Space_schemePointTopology_of_isAffine c.scheme
  refine ⟨Set.range g, hg.isOpen_range, ⟨⟨u, huN⟩, rfl⟩,
    e.symm.isEmbedding.t2Space, fun _ => ?_, fun _ => ?_⟩
  · have : LocallyCompactSpace (RingPoints K X K) :=
      locallyCompactSpace_etaleChartTopology hK hX.1
    exact hg.isOpen_range.locallyCompactSpace
  · have : TotallyDisconnectedSpace (RingPoint K c.scheme K) :=
      totallyDisconnectedSpace_schemePointTopology_of_isAffine c.scheme
    exact e.totallyDisconnectedSpace

end Langlands.AlgebraicGeometry.AlgebraicSpace
