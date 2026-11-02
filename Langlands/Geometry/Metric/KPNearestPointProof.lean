import Langlands.Geometry.Metric.KPNearestPointStatement
import Langlands.Geometry.Metric.KPGeodesicUniquenessProof
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.MetricSpace.Cauchy

/-! # Nearest-point projection in complete KP NPC geodesic spaces -/

noncomputable section

open Set unitInterval Filter Topology

namespace Langlands.Geometry.Metric.KP

universe uX

variable {X : Type*} [MetricSpace X]

/-- A lower bound for distances to a convex set gives the squared midpoint deficit. -/
theorem dist_sq_le_nearest_deficit (hX : IsNonpositivelyCurved X)
    (hgeo : IsGeodesicSpace X) {Y : Set X} (hc : IsGeodesicallyConvex Y)
    (x : X) {r : ℝ} (hr0 : 0 ≤ r) (hr : ∀ y ∈ Y, r ≤ dist x y)
    {y z : X} (hy : y ∈ Y) (hz : z ∈ Y) :
    dist y z ^ 2 ≤ 2 * dist x y ^ 2 + 2 * dist x z ^ 2 - 4 * r ^ 2 := by
  obtain ⟨γ, hγ⟩ := hgeo y z
  let t : I := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  have hmY := hc.apply_mem hy hz hγ t
  have hr2 := (sq_le_sq₀ hr0 dist_nonneg).mpr (hr (γ t) hmY)
  have hmid := hγ.isNPCMidpoint hX x
  change 2 * dist (γ t) x ^ 2 + (1 / 2) * dist y z ^ 2 ≤
    dist y x ^ 2 + dist z x ^ 2 at hmid
  rw [dist_comm (γ t) x, dist_comm y x, dist_comm z x] at hmid
  linarith

/-- A distance-minimizing sequence is Cauchy, and closedness retains its limit in the set. -/
theorem exists_nearestPoint [CompleteSpace X] (hX : IsNonpositivelyCurved X)
    (hgeo : IsGeodesicSpace X) {Y : Set X} (hclosed : IsClosed Y)
    (hc : IsGeodesicallyConvex Y) (x : X) :
    ∃ p : Y, ∀ y : Y, dist x (p : X) ≤ dist x (y : X) := by
  let D : Set ℝ := dist x '' Y
  let r : ℝ := sInf D
  have hne : D.Nonempty := hc.1.image (dist x)
  have hzero : 0 ∈ lowerBounds D := by
    rintro _ ⟨y, _, rfl⟩
    exact dist_nonneg
  have hglb : IsGLB D r := isGLB_csInf hne ⟨0, hzero⟩
  have hr0 : 0 ≤ r := hglb.2 hzero
  have hr : ∀ y ∈ Y, r ≤ dist x y := fun y hy => hglb.1 ⟨y, hy, rfl⟩
  obtain ⟨v, _, _, hvlim, hv⟩ := hglb.exists_seq_antitone_tendsto hne
  have hchoose : ∀ n, ∃ y ∈ Y, dist x y = v n := hv
  choose u huY huv using hchoose
  have hulim : Tendsto (fun n => dist x (u n)) atTop (𝓝 r) := by
    simpa only [huv] using hvlim
  have hCauchy : CauchySeq u := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    have hε2 : 0 < ε ^ 2 / 4 := by positivity
    have hev := (hulim.pow 2).eventually
      (gt_mem_nhds (show r ^ 2 < r ^ 2 + ε ^ 2 / 4 by linarith))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    refine ⟨N, fun i hi j hj => ?_⟩
    have hgap := dist_sq_le_nearest_deficit hX hgeo hc x hr0 hr (huY i) (huY j)
    have hi' := hN i hi
    have hj' := hN j hj
    nlinarith [dist_nonneg (x := u i) (y := u j)]
  obtain ⟨p, hplim⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hpY := hclosed.mem_of_tendsto hplim (Eventually.of_forall huY)
  have hpr : dist x p = r :=
    tendsto_nhds_unique (tendsto_const_nhds.dist hplim) hulim
  refine ⟨⟨p, hpY⟩, fun y => ?_⟩
  change dist x p ≤ dist x (y : X)
  rw [hpr]
  exact hr y y.property

/-- A point at the same distance as a nearest point must equal that point. -/
theorem nearestPoint_unique (hX : IsNonpositivelyCurved X)
    (hgeo : IsGeodesicSpace X) {Y : Set X} (hc : IsGeodesicallyConvex Y)
    (x : X) (p : Y) (hp : ∀ y : Y, dist x (p : X) ≤ dist x (y : X))
    (q : Y) (hq : dist x (q : X) = dist x (p : X)) : q = p := by
  have hgap := dist_sq_le_nearest_deficit hX hgeo hc x dist_nonneg
    (fun y hy => hp ⟨y, hy⟩) q.property p.property
  rw [hq] at hgap
  apply Subtype.ext
  apply dist_eq_zero.mp
  nlinarith [sq_nonneg (dist (q : X) (p : X)),
    dist_nonneg (x := (q : X)) (y := (p : X))]

/-- The distance squeeze and squared midpoint estimate prove continuity without division. -/
theorem continuous_of_nearestPoint (hX : IsNonpositivelyCurved X)
    (hgeo : IsGeodesicSpace X) {Y : Set X} (hc : IsGeodesicallyConvex Y)
    (π : X → Y) (hπ : ∀ (x : X) (y : Y), dist x (π x : X) ≤ dist x (y : X)) :
    Continuous π := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let r : ℝ := dist x (π x : X)
  let q : X → ℝ := fun z => dist x (π z : X)
  have hupper : Tendsto (fun z : X => dist x z + dist z (π x : X))
      (𝓝 x) (𝓝 r) := by
    have h : Tendsto (fun z : X => dist x z + dist z (π x : X))
        (𝓝 x) (𝓝 (dist x x + dist x (π x : X))) :=
      (tendsto_const_nhds.dist tendsto_id).add (tendsto_id.dist tendsto_const_nhds)
    simpa only [dist_self, zero_add] using h
  have hq : Tendsto q (𝓝 x) (𝓝 r) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · exact fun z => hπ x (π z)
    · intro z
      exact (dist_triangle x z (π z : X)).trans (add_le_add le_rfl (hπ z (π x)))
  have hdeficit : Tendsto (fun z => 2 * q z ^ 2 - 2 * r ^ 2) (𝓝 x) (𝓝 0) := by
    have htwo : Tendsto (fun _ : X => (2 : ℝ)) (𝓝 x) (𝓝 2) := tendsto_const_nhds
    simpa using (htwo.mul (hq.pow 2)).sub
      (tendsto_const_nhds : Tendsto (fun _ : X => 2 * r ^ 2) (𝓝 x) (𝓝 (2 * r ^ 2)))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hev := hdeficit.eventually (gt_mem_nhds (show (0 : ℝ) < ε ^ 2 by positivity))
  filter_upwards [hev] with z hz
  have hgap := dist_sq_le_nearest_deficit hX hgeo hc x dist_nonneg
    (fun y hy => hπ x ⟨y, hy⟩) (π z).property (π x).property
  change dist (π z : X) (π x : X) < ε
  change 2 * dist x (π z : X) ^ 2 - 2 * dist x (π x : X) ^ 2 < ε ^ 2 at hz
  nlinarith [dist_nonneg (x := (π z : X)) (y := (π x : X))]

/-- Minimality, distance preservation and uniqueness give simultaneous equivariance. -/
theorem nearestPoint_isometry (hX : IsNonpositivelyCurved X)
    (hgeo : IsGeodesicSpace X) {Y : Set X} (hc : IsGeodesicallyConvex Y)
    (π : X → Y) (hπ : ∀ (x : X) (y : Y), dist x (π x : X) ≤ dist x (y : X))
    (e : X ≃ᵢ X) (he : e '' Y = Y) (x : X) :
    (π (e x) : X) = e (π x : X) := by
  have he_mem : e (π x : X) ∈ Y := by
    exact he.subset (mem_image_of_mem e (π x).property)
  let ep : Y := ⟨e (π x : X), he_mem⟩
  have hpim : (π (e x) : X) ∈ e '' Y := by
    exact he.symm.subset (π (e x)).property
  obtain ⟨z, hz, hze⟩ := hpim
  have hreverse : dist (e x) (ep : X) ≤ dist (e x) (π (e x) : X) := by
    change dist (e x) (e (π x : X)) ≤ dist (e x) (π (e x) : X)
    rw [← hze, e.dist_eq, e.dist_eq]
    exact hπ x ⟨z, hz⟩
  have hequal : ep = π (e x) :=
    nearestPoint_unique hX hgeo hc (e x) (π (e x)) (hπ (e x)) ep
      (le_antisymm hreverse (hπ (e x) ep))
  exact (congrArg Subtype.val hequal).symm

/-- KP Proposition 1.1.20, with the exact published universe-polymorphic target. -/
theorem nearestPointProjection : NearestPointProjectionStatement.{uX} := by
  intro X _ _ hX hgeo Y hclosed hc
  have hex := fun x : X => exists_nearestPoint hX hgeo hclosed hc x
  choose π hπ using hex
  refine ⟨π, hπ, ?_, continuous_of_nearestPoint hX hgeo hc π hπ, ?_⟩
  · exact fun x y hy => nearestPoint_unique hX hgeo hc x (π x) (hπ x) y hy
  · exact fun e he x => nearestPoint_isometry hX hgeo hc π hπ e he x

end Langlands.Geometry.Metric.KP
