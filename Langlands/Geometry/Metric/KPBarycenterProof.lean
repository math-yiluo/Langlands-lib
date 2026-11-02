import Langlands.Geometry.Metric.KPGeodesicUniquenessProof
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.MetricSpace.Cauchy

/-! # Barycenters of closed bounded convex sets in complete NPC geodesic spaces -/

noncomputable section

open Set Bornology unitInterval Filter Topology

namespace Langlands.Geometry.Metric.KP

universe uX

variable {X : Type*} [MetricSpace X]

/-- Taking the supremum in the primitive NPC inequality preserves its squared estimate. -/
theorem IsNPCMidpoint.jointDiam_sq_le {x y m : X} (hm : IsNPCMidpoint x y m)
    {M : Set X} (hne : M.Nonempty) (hb : IsBounded M) :
    2 * (jointDiam {m} M).toReal ^ 2 + (1 / 2) * dist x y ^ 2 ≤
      (jointDiam {x} M).toReal ^ 2 + (jointDiam {y} M).toReal ^ 2 := by
  obtain ⟨v, _, _, hvlim, hv⟩ :=
    (isLUB_toReal_jointDiam_singleton m hne hb).exists_seq_monotone_tendsto
      (hne.image (dist m))
  apply le_of_tendsto' ((tendsto_const_nhds.mul (hvlim.pow 2)).add tendsto_const_nhds)
  intro n
  obtain ⟨z, hz, hzv⟩ := hv n
  rw [← hzv]
  have hx := (isLUB_toReal_jointDiam_singleton x hne hb).1 ⟨z, hz, rfl⟩
  have hy := (isLUB_toReal_jointDiam_singleton y hne hb).1 ⟨z, hz, rfl⟩
  have hx2 := (sq_le_sq₀ dist_nonneg ENNReal.toReal_nonneg).mpr hx
  have hy2 := (sq_le_sq₀ dist_nonneg ENNReal.toReal_nonneg).mpr hy
  exact (hm z).trans (add_le_add hx2 hy2)

/-- Two centers are close whenever their squared joint diameters approach the squared radius. -/
theorem dist_sq_le_jointDiam_deficit (hX : IsNonpositivelyCurved X)
    (hgeo : IsGeodesicSpace X) {M : Set X} (hb : IsBounded M)
    (hc : IsGeodesicallyConvex M) {x y : X} (hx : x ∈ M) (hy : y ∈ M) :
    dist x y ^ 2 ≤ 2 * (jointDiam {x} M).toReal ^ 2 +
      2 * (jointDiam {y} M).toReal ^ 2 - 4 * (radius M).toReal ^ 2 := by
  obtain ⟨γ, hγ⟩ := hgeo x y
  let t : I := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  have hmM := hc.apply_mem hx hy hγ t
  have hr := (isGLB_toReal_radius hc.1 hb).1 ⟨γ t, hmM, rfl⟩
  have hr2 := (sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mpr hr
  have hmid := (hγ.isNPCMidpoint hX).jointDiam_sq_le hc.1 hb
  change 2 * (jointDiam {γ t} M).toReal ^ 2 + (1 / 2) * dist x y ^ 2 ≤
    (jointDiam {x} M).toReal ^ 2 + (jointDiam {y} M).toReal ^ 2 at hmid
  linarith

/-- A minimizing sequence is Cauchy by the squared midpoint deficit and converges in the set. -/
theorem exists_isBarycenter [CompleteSpace X] (hX : IsNonpositivelyCurved X)
    (hgeo : IsGeodesicSpace X) {M : Set X} (hb : IsBounded M) (hclosed : IsClosed M)
    (hc : IsGeodesicallyConvex M) : ∃ b : X, IsBarycenter M b := by
  let f : X → ℝ := fun x => (jointDiam {x} M).toReal
  let r : ℝ := (radius M).toReal
  obtain ⟨v, _, _, hvlim, hv⟩ :=
    (isGLB_toReal_radius hc.1 hb).exists_seq_antitone_tendsto (hc.1.image f)
  have hchoose : ∀ n, ∃ x ∈ M, f x = v n := hv
  choose u huM huf using hchoose
  have hflim : Tendsto (fun n => f (u n)) atTop (𝓝 r) := by
    simpa only [huf] using hvlim
  have hCauchy : CauchySeq u := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    have hε2 : 0 < ε ^ 2 / 4 := by positivity
    have hev := (hflim.pow 2).eventually
      (gt_mem_nhds (show r ^ 2 < r ^ 2 + ε ^ 2 / 4 by linarith))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    refine ⟨N, fun i hi j hj => ?_⟩
    have hgap := dist_sq_le_jointDiam_deficit hX hgeo hb hc (huM i) (huM j)
    change dist (u i) (u j) ^ 2 ≤ 2 * f (u i) ^ 2 + 2 * f (u j) ^ 2 - 4 * r ^ 2 at hgap
    have hi' := hN i hi
    have hj' := hN j hj
    nlinarith [dist_nonneg (x := u i) (y := u j)]
  obtain ⟨b, hblim⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hbM := hclosed.mem_of_tendsto hblim (Eventually.of_forall huM)
  refine ⟨b, (isBarycenter_iff_toReal hb).mpr ⟨hbM, le_antisymm ?_ ?_⟩⟩
  · apply (isLUB_toReal_jointDiam_singleton b hc.1 hb).2
    rintro _ ⟨z, hz, rfl⟩
    apply le_of_tendsto_of_tendsto' (hblim.dist tendsto_const_nhds) hflim
    intro n
    exact (isLUB_toReal_jointDiam_singleton (u n) hc.1 hb).1 ⟨z, hz, rfl⟩
  · exact (isGLB_toReal_radius hc.1 hb).1 ⟨b, hbM, rfl⟩

/-- The squared midpoint estimate forces any two barycenters to coincide. -/
theorem IsBarycenter.eq (hX : IsNonpositivelyCurved X) (hgeo : IsGeodesicSpace X)
    {M : Set X} (hb : IsBounded M) (hc : IsGeodesicallyConvex M) {x y : X}
    (hx : IsBarycenter M x) (hy : IsBarycenter M y) : x = y := by
  have hgap := dist_sq_le_jointDiam_deficit hX hgeo hb hc hx.1 hy.1
  rw [hx.2, hy.2] at hgap
  apply dist_eq_zero.mp
  nlinarith [sq_nonneg (dist x y), dist_nonneg (x := x) (y := y)]

/-- Joint diameter is unchanged by simultaneous transport of a center and its set. -/
theorem jointDiam_singleton_isometry_image (e : X ≃ᵢ X) (x : X) (M : Set X) :
    jointDiam {e x} (e '' M) = jointDiam {x} M := by
  rw [jointDiam_singleton_left, jointDiam_singleton_left]
  apply le_antisymm
  · refine iSup₂_le fun z hz => ?_
    obtain ⟨w, hw, rfl⟩ := hz
    rw [e.edist_eq]
    exact le_iSup₂_of_le w hw le_rfl
  · refine iSup₂_le fun z hz => ?_
    exact le_iSup₂_of_le (e z) (mem_image_of_mem e hz) (e.edist_eq x z).symm.le

/-- A set-preserving isometry sends every barycenter to a barycenter of the same set. -/
theorem IsBarycenter.isometry (e : X ≃ᵢ X) {M : Set X} (he : e '' M = M) {b : X}
    (hb : IsBarycenter M b) : IsBarycenter M (e b) := by
  refine ⟨?_, ?_⟩
  · rw [← he]
    exact mem_image_of_mem e hb.1
  · rw [← he, jointDiam_singleton_isometry_image, he]
    exact hb.2

/-- KP Theorem 1.1.15(1), with the exact published universe-polymorphic target. -/
theorem barycenter : BarycenterStatement.{uX} := by
  intro X _ _ hX hgeo M hb hclosed hc
  obtain ⟨b, hbary⟩ := exists_isBarycenter hX hgeo hb hclosed hc
  refine ⟨⟨b, hbary, fun c hcary => hcary.eq hX hgeo hb hc hbary⟩, ?_⟩
  intro c hcary e he
  exact (hcary.isometry e he).eq hX hgeo hb hc hcary

end Langlands.Geometry.Metric.KP
