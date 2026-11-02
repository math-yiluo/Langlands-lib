import Langlands.Geometry.Metric.KPCompleteNPCGeodesicStatement
import Mathlib.Topology.Order.Monotone

/-! # Geodesics from completeness and the primitive NPC inequality -/

noncomputable section

open Set unitInterval

namespace Langlands.Geometry.Metric.KP

universe uX

variable {X : Type*} [MetricSpace X]

/-- On the triangle-equality locus, distance from the first endpoint preserves distances. -/
theorem dist_eq_abs_sub_of_dist_add_eq (hX : IsNonpositivelyCurved X) {x y p q : X}
    (hp : dist x p + dist p y = dist x y)
    (hq : dist x q + dist q y = dist x y) :
    dist p q = |dist x p - dist x q| := by
  refine le_antisymm ?_ ?_
  · by_contra h
    have hlt : |dist x p - dist x q| < dist p q := lt_of_not_ge h
    have hs : (dist x p - dist x q) ^ 2 < dist p q ^ 2 := by
      have := (sq_lt_sq₀ (abs_nonneg (dist x p - dist x q))
        (dist_nonneg (x := p) (y := q))).mpr hlt
      simpa only [sq_abs] using this
    obtain ⟨m, hm⟩ := hX p q
    have hx := hm x
    have hy := hm y
    rw [dist_comm p x, dist_comm q x, dist_comm m x] at hx
    have hx2 : dist x m ^ 2 < ((dist x p + dist x q) / 2) ^ 2 := by
      nlinarith
    have hdiff : dist p y - dist q y = -(dist x p - dist x q) := by linarith
    have hs' : (dist p y - dist q y) ^ 2 < dist p q ^ 2 := by
      rwa [hdiff, neg_sq]
    have hy2 : dist m y ^ 2 < ((dist p y + dist q y) / 2) ^ 2 := by
      nlinarith
    have hxlt : dist x m < (dist x p + dist x q) / 2 :=
      (sq_lt_sq₀ dist_nonneg (by positivity)).mp hx2
    have hylt : dist m y < (dist p y + dist q y) / 2 :=
      (sq_lt_sq₀ dist_nonneg (by positivity)).mp hy2
    have := dist_triangle x m y
    linarith
  · simpa only [dist_comm p x, dist_comm q x] using abs_dist_sub_le p q x

/-- An NPC midpoint between ordered points of a metric segment is again on that segment,
and its endpoint distance is the arithmetic mean. -/
theorem IsNPCMidpoint.dist_add_eq_and_dist_eq_mean (hX : IsNonpositivelyCurved X)
    {x y p q m : X} (hp : dist x p + dist p y = dist x y)
    (hq : dist x q + dist q y = dist x y)
    (hpq : dist x p ≤ dist x q) (hm : IsNPCMidpoint p q m) :
    dist x m + dist m y = dist x y ∧
      dist x m = (dist x p + dist x q) / 2 := by
  have hd : dist p q = dist x q - dist x p := by
    rw [dist_eq_abs_sub_of_dist_add_eq hX hp hq, abs_of_nonpos (sub_nonpos.mpr hpq)]
    ring
  have hl := hm.dist_left
  have hr := hm.dist_right
  rw [hd] at hl hr
  have h₁ := dist_triangle x p m
  have h₂ := dist_triangle x m q
  have h₃ := dist_triangle m q y
  have h₄ := dist_triangle x m y
  rw [dist_comm m q] at h₂ h₃
  constructor <;> linarith

/-- A closed real set containing both endpoints and closed under arithmetic means
contains the full interval. The proof excludes a gap using its extremal endpoints. -/
private theorem Icc_subset_of_isClosed_of_mean_mem {S : Set ℝ} (hS : IsClosed S)
    {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S)
    (hmean : ∀ r ∈ S, ∀ s ∈ S, (r + s) / 2 ∈ S) :
    Icc a b ⊆ S := by
  intro t ht
  let L := S ∩ Iic t
  let R := S ∩ Ici t
  have hLne : L.Nonempty := ⟨a, ha, ht.1⟩
  have hRne : R.Nonempty := ⟨b, hb, ht.2⟩
  have hLb : BddAbove L := ⟨t, fun _ hr => hr.2⟩
  have hRb : BddBelow R := ⟨t, fun _ hr => hr.2⟩
  have hLmem : sSup L ∈ L := (hS.inter isClosed_Iic).csSup_mem hLne hLb
  have hRmem : sInf R ∈ R := (hS.inter isClosed_Ici).csInf_mem hRne hRb
  have hM : (sSup L + sInf R) / 2 ∈ S := hmean _ hLmem.1 _ hRmem.1
  by_cases htS : t ∈ S
  · exact htS
  · have hlt : sSup L < t := lt_of_le_of_ne hLmem.2 (by
      intro h
      exact htS (h ▸ hLmem.1))
    have htr : t < sInf R := lt_of_le_of_ne hRmem.2 (by
      intro h
      exact htS (h ▸ hRmem.1))
    rcases le_or_gt ((sSup L + sInf R) / 2) t with hm | hm
    · have := le_csSup hLb (show (sSup L + sInf R) / 2 ∈ L from ⟨hM, hm⟩)
      linarith
    · have := csInf_le hRb (show (sSup L + sInf R) / 2 ∈ R from ⟨hM, hm.le⟩)
      linarith

/-- The complete triangle-equality locus contains a point at every endpoint distance. -/
theorem exists_dist_eq_of_complete_npc [CompleteSpace X] (hX : IsNonpositivelyCurved X)
    (x y : X) {r : ℝ} (hr : r ∈ Icc 0 (dist x y)) :
    ∃ p : X, dist x p + dist p y = dist x y ∧ dist x p = r := by
  let M : Set X := {p | dist x p + dist p y = dist x y}
  have hM : IsClosed M :=
    isClosed_eq ((continuous_const.dist continuous_id).add
      (continuous_id.dist continuous_const)) continuous_const
  let : CompleteSpace M := hM.isComplete.completeSpace_coe
  let f : M → ℝ := fun p => dist x p
  have hf : Isometry f := Isometry.of_dist_eq fun p q => by
    change |dist x (p : X) - dist x (q : X)| = dist (p : X) (q : X)
    exact (dist_eq_abs_sub_of_dist_add_eq hX p.property q.property).symm
  have hS : IsClosed (range f) := hf.isClosedEmbedding.isClosed_range
  have h0 : 0 ∈ range f := ⟨⟨x, by simp [M]⟩, by simp [f]⟩
  have h1 : dist x y ∈ range f := ⟨⟨y, by simp [M]⟩, rfl⟩
  have hmean : ∀ a ∈ range f, ∀ b ∈ range f, (a + b) / 2 ∈ range f := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    obtain ⟨m, hm⟩ := hX (p : X) (q : X)
    rcases le_total (dist x (p : X)) (dist x (q : X)) with hpq | hqp
    · have h := hm.dist_add_eq_and_dist_eq_mean hX p.property q.property hpq
      exact ⟨⟨m, h.1⟩, h.2⟩
    · have hm' : IsNPCMidpoint (q : X) (p : X) m := by
        intro z
        simpa only [dist_comm (q : X) (p : X), add_comm] using hm z
      have h := hm'.dist_add_eq_and_dist_eq_mean hX q.property p.property hqp
      exact ⟨⟨m, h.1⟩, h.2.trans (by dsimp [f]; ring)⟩
  obtain ⟨p, hp⟩ := Icc_subset_of_isClosed_of_mean_mem hS h0 h1 hmean hr
  exact ⟨p, p.property, hp⟩

/-- Completeness and the primitive KP midpoint condition supply geodesic paths. -/
theorem isGeodesicSpace_of_complete_npc [CompleteSpace X] (hX : IsNonpositivelyCurved X) :
    IsGeodesicSpace X := by
  intro x y
  have hex : ∀ t : I, ∃ p : X,
      dist x p + dist p y = dist x y ∧ dist x p = (t : ℝ) * dist x y := by
    intro t
    apply exists_dist_eq_of_complete_npc hX x y
    constructor
    · exact mul_nonneg (nonneg t) dist_nonneg
    · exact mul_le_of_le_one_left dist_nonneg (le_one t)
  choose c hc hdist using hex
  have hlaw : ∀ s t : I, dist (c s) (c t) = dist x y * |(s : ℝ) - t| := by
    intro s t
    rw [dist_eq_abs_sub_of_dist_add_eq hX (hc s) (hc t), hdist, hdist,
      ← sub_mul, abs_mul, abs_of_nonneg (dist_nonneg (x := x) (y := y)), mul_comm]
  have hcont : Continuous c := by
    have hLip : LipschitzWith ⟨dist x y, dist_nonneg⟩ c :=
      LipschitzWith.of_dist_le_mul fun s t => by
        rw [hlaw]
        rfl
    exact hLip.continuous
  have hc0 : c 0 = x := by
    have h := hdist 0
    simp only [Icc.coe_zero, zero_mul, dist_eq_zero] at h
    exact h.symm
  have hc1 : c 1 = y := by
    have h := hc 1
    rw [hdist] at h
    simp only [Icc.coe_one, one_mul] at h
    exact dist_eq_zero.mp (by linarith)
  exact ⟨⟨⟨c, hcont⟩, hc0, hc1⟩, hlaw⟩

/-- The exact universe-polymorphic published geodesic-existence target. -/
theorem completeNPCGeodesic : CompleteNPCGeodesicStatement.{uX} := by
  intro X _ _ hX
  exact isGeodesicSpace_of_complete_npc hX

end Langlands.Geometry.Metric.KP
