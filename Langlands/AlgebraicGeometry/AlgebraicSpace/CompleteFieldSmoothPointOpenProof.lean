import Langlands.AlgebraicGeometry.AlgebraicSpace.CompleteFieldSmoothPointOpenStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartOpenMap
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianFinitePointProperProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothMorphismCharts
import Langlands.AlgebraicGeometry.PointTopology.CompleteFieldSmoothOpenProof
import Langlands.AlgebraicGeometry.PointTopology.CompleteHenselianValuedFieldProof

/-! # Smooth maps of algebraic spaces are open on points over complete fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint schemePointTopology IsHenselianValuedField schemePointContinuity_proof)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open HenselianFinitePointProperProof in
/-- **Smooth maps are open on rational points over complete fields.** Let `x` be a rational
point of `X`. Choose finite-type étale charts `c` of `X` through `x` and `d` of `Y` through
`f x`, and let `W` be the scheme representing `c ×_Y d`. Its projection to `c` is étale, so
`W → d` is a chart square of `f` and is smooth. Points of `W` map to `X(K)` continuously,
`W(K) → d(K)` is open by the scheme theorem, and `d(K) → Y(K)` is open; the image of a
neighbourhood of `x` therefore contains an open neighbourhood of `f x`. -/
theorem completeFieldSmoothSpacePointOpen : CompleteFieldSmoothSpacePointOpenStatement.{u} := by
  intro K _ _ X Y hXs hXl hYs hYl f hf
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  let : TopologicalSpace (RingPoints K Y K) := etaleChartTopology K Y
  have hK : IsHenselianValuedField K := PointTopology.completeHenselianValuedField K
  intro N hN
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨x, hxN, rfl⟩
  obtain ⟨c, u, hu⟩ := exists_chart_pointMap_eq (isQuasiSeparated_of_isSeparated hXs) hXl x
  obtain ⟨d, v, hv⟩ :=
    exists_chart_pointMap_eq (isQuasiSeparated_of_isSeparated hYs) hYl (RingPoints.map f x)
  have := c.locallyOfFiniteType
  have := d.locallyOfFiniteType
  let a : (schemeYoneda _).obj c.scheme ⟶ Y.presheaf := hom c.hom ≫ hom f
  let b : (schemeYoneda _).obj d.scheme ⟶ Y.presheaf := hom d.hom
  have hfst : Etale (pairPullbackFst a b).left := etale_pairPullbackFst a b d.isEtale
  have : LocallyOfFiniteType (pairPullback a b).hom :=
    locallyOfFiniteType_pairPullback a b d.isEtale
  have hsq : ((schemeYoneda _).map (pairPullbackFst a b) ≫ hom c.hom) ≫ hom f =
      (schemeYoneda _).map (pairPullbackSnd a b) ≫ b :=
    (Category.assoc _ _ _).trans (pairPullback_isPullback a b).w
  have hWet : IsEtale ((schemeYoneda _).map (pairPullbackFst a b) ≫ hom c.hom) :=
    IsEtale.comp (isEtale_map _ hfst) c.isEtale
  have : Smooth (pairPullbackSnd a b).left := hf.smooth_chart _ b _ hWet d.isEtale hsq
  have hpt : schemePointsMap a u = schemePointsMap b v := by
    change RingPoints.map f (c.pointMap u) = d.pointMap v
    rw [hu, hv]
  obtain ⟨w, hw₁, hw₂⟩ := exists_pairPullback_point a b hpt
  let : TopologicalSpace (RingPoint K (pairPullback a b) K) :=
    schemePointTopology K (pairPullback a b) K
  let : TopologicalSpace (RingPoint K c.scheme K) := schemePointTopology K c.scheme K
  let : TopologicalSpace (RingPoint K d.scheme K) := schemePointTopology K d.scheme K
  let ψ : RingPoint K (pairPullback a b) K → RingPoints K X K :=
    fun w' => c.pointMap (w' ≫ pairPullbackFst a b)
  have hψ : Continuous ψ :=
    c.continuous_pointMap.comp (schemePointContinuity_proof K K _ _ (pairPullbackFst a b))
  let φ : RingPoint K (pairPullback a b) K → RingPoint K d.scheme K :=
    fun w' => w' ≫ pairPullbackSnd a b
  have hφ : IsOpenMap φ :=
    PointTopology.completeFieldSmoothPointOpen K (pairPullback a b) d.scheme
      (pairPullbackSnd a b)
  have hd : IsOpenMap d.pointMap := d.isOpenMap_pointMap hK
  refine ⟨d.pointMap '' (φ '' (ψ ⁻¹' N)), ?_, hd _ (hφ _ (hN.preimage hψ)), ?_⟩
  · rintro _ ⟨_, ⟨w', hw', rfl⟩, rfl⟩
    exact ⟨ψ w', hw', schemePointsMap_pairPullbackFst a b w'⟩
  · refine ⟨φ w, ⟨w, ?_, rfl⟩, ?_⟩
    · change c.pointMap (w ≫ pairPullbackFst a b) ∈ N
      rw [hw₁, hu]
      exact hxN
    · change d.pointMap (w ≫ pairPullbackSnd a b) = RingPoints.map f x
      rw [hw₂, hv]

end Langlands.AlgebraicGeometry.AlgebraicSpace
