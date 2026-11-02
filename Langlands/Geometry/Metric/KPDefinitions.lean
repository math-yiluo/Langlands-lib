import Mathlib.Topology.Subpath
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.EMetricSpace.Diam
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.InnerProductSpace.Convex

/-!
# Metric geodesics, nonpositive curvature and barycenters (Kaletha–Prasad, §1.1)

This module records the metric-space definitions of Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Section 1.1, with the authors' corrections of 1 November 2024, over Mathlib
metric spaces:

* the length (1.1.1) of a curve `[0,1] → X`, rectifiability and the literal geodesic condition
  of Definition 1.1.2, together with the normalized constant-speed distance law on Mathlib paths
  and a proof that the two agree;
* geodesic and uniquely geodesic spaces (Definition 1.1.4);
* the nonpositive-curvature midpoint inequality (Definition 1.1.8);
* convex sets (corrected Definition 1.1.12(1)), the joint diameter (Definition 1.1.1(2)),
  radius and barycenters (Definition 1.1.12(2),(3));
* the closed convex hull (Definition 1.1.14) and bounded actions (Lemma 1.1.17,
  Definition 1.1.18).

Lemma 1.1.11, Lemma 1.1.13, Theorem 1.1.15 and Corollary 1.1.19 are *not* proved or assumed here.
-/

noncomputable section

open Set Bornology unitInterval
open scoped ENNReal

namespace Langlands.Geometry.Metric.KP

variable {X : Type*} [MetricSpace X]

/-! ### Curves, partitions and length -/

/-- A finite sequence `0 = t₀ < t₁ < ⋯ < tₙ = 1` in `[0,1]`, as in the supremum (1.1.1). -/
def IsUnitPartition {n : ℕ} (t : Fin (n + 1) → I) : Prop :=
  StrictMono t ∧ t 0 = 0 ∧ t (Fin.last n) = 1

/-- The polygonal sum `∑_{i < n} d(c(tᵢ), c(tᵢ₊₁))` of (1.1.1), valued in `[0, ∞]`. -/
def partitionSum (c : I → X) {n : ℕ} (t : Fin (n + 1) → I) : ℝ≥0∞ :=
  ∑ i : Fin n, edist (c (t i.castSucc)) (c (t i.succ))

/-- KP (1.1.1): the length of a curve `c : [0,1] → X`, the supremum of the polygonal sums over
all finite sequences `0 = t₀ < ⋯ < tₙ = 1`, valued in `[0, ∞]`. -/
def curveLength (c : I → X) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (t : Fin (n + 1) → I) (_ : IsUnitPartition t), partitionSum c t

/-- KP Definition 1.1.2(1): a curve is rectifiable if its length is finite. -/
def IsRectifiable (c : C(I, X)) : Prop :=
  curveLength c < ⊤

/-- The source restriction `c|[t₁,t₂] : [0,1] → X`, `s ↦ c(t₁ + s(t₂ - t₁))`
(KP Definition 1.1.2(2)). Mathlib's `Set.Icc.convexComb t₁ t₂ s` is `(1 - s) t₁ + s t₂`. -/
def curveRestrict (c : I → X) (t₁ t₂ : I) : I → X :=
  c ∘ Set.Icc.convexComb t₁ t₂

/-- KP Definition 1.1.2(2), literally: a curve is geodesic if it is rectifiable and for all
`0 < t₁ < t₂ < 1` one has `ℓ(c|[t₁,t₂]) = d(c(t₁), c(t₂)) = d(c(0), c(1)) |t₁ - t₂|`. -/
def IsSourceGeodesic (c : C(I, X)) : Prop :=
  IsRectifiable c ∧ ∀ t₁ t₂ : I, 0 < t₁ → t₁ < t₂ → t₂ < 1 →
    curveLength (curveRestrict c t₁ t₂) = edist (c t₁) (c t₂) ∧
      dist (c t₁) (c t₂) = dist (c 0) (c 1) * |(t₁ : ℝ) - t₂|

/-- The normalized constant-speed distance law for a map `c : [0,1] → X`:
`d(c(s), c(t)) = d(c(0), c(1)) |s - t|` for all `s, t ∈ [0,1]`. -/
def IsGeodesicCurve (c : I → X) : Prop :=
  ∀ s t : I, dist (c s) (c t) = dist (c 0) (c 1) * |(s : ℝ) - t|

/-- A geodesic segment joining `x` to `y`: a Mathlib path `γ` with `γ 0 = x`, `γ 1 = y`
satisfying `d(γ(s), γ(t)) = d(x, y) |s - t|`. By `isGeodesic_iff_isSourceGeodesic` this is
exactly a geodesic curve joining `x` and `y` in the sense of KP Definition 1.1.2. -/
def IsGeodesic {x y : X} (γ : Path x y) : Prop :=
  ∀ s t : I, dist (γ s) (γ t) = dist x y * |(s : ℝ) - t|

variable (X) in
/-- KP Definition 1.1.4: a metric space is geodesic if any two points are joined by a geodesic. -/
def IsGeodesicSpace : Prop :=
  ∀ x y : X, ∃ γ : Path x y, IsGeodesic γ

variable (X) in
/-- KP Definition 1.1.4: a metric space is uniquely geodesic if any two points are joined by a
geodesic and that geodesic is unique. -/
def IsUniquelyGeodesicSpace : Prop :=
  ∀ x y : X, ∃! γ : Path x y, IsGeodesic γ

/-! ### Source-length comparison -/

theorem sum_succ_sub_castSucc {n : ℕ} (f : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.succ_castSucc]
    rw [ih (fun i => f i.castSucc)]
    simp only [Fin.succ_last, Fin.castSucc_zero]
    ring

/-- For a curve satisfying the distance law, every polygonal sum along a monotone sequence
`t₀ ≤ ⋯ ≤ tₙ` telescopes to `d(c(0), c(1)) (tₙ - t₀)`. -/
theorem partitionSum_eq_of_isGeodesicCurve {c : I → X} (hc : IsGeodesicCurve c) {n : ℕ}
    (t : Fin (n + 1) → I) (ht : Monotone t) :
    partitionSum c t = ENNReal.ofReal (dist (c 0) (c 1) * ((t (Fin.last n) : ℝ) - t 0)) := by
  have hle : ∀ i : Fin n, (t i.castSucc : ℝ) ≤ t i.succ := fun i =>
    Subtype.coe_le_coe.mpr (ht Fin.castSucc_lt_succ.le)
  have hterm : ∀ i : Fin n, edist (c (t i.castSucc)) (c (t i.succ)) =
      ENNReal.ofReal (dist (c 0) (c 1) * ((t i.succ : ℝ) - t i.castSucc)) := by
    intro i
    rw [edist_dist, hc, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hle i))]
  rw [partitionSum, Finset.sum_congr rfl (fun i _ => hterm i),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg dist_nonneg (sub_nonneg.mpr (hle i))),
    ← Finset.mul_sum, sum_succ_sub_castSucc (fun i => (t i : ℝ))]

/-- The endpoint distance is at most the length of any curve (the remark after KP Remark 1.1.3,
using the partition `0 < 1`). -/
theorem edist_le_curveLength (c : I → X) : edist (c 0) (c 1) ≤ curveLength c := by
  have h01 : (0 : I) < 1 := by
    rw [← Subtype.coe_lt_coe]
    norm_num
  have hpart : IsUnitPartition (![0, 1] : Fin 2 → I) := by
    refine ⟨Fin.strictMono_iff_lt_succ.mpr fun i => ?_, rfl, rfl⟩
    fin_cases i
    simp [h01]
  have hsum : partitionSum c (![0, 1] : Fin 2 → I) = edist (c 0) (c 1) := by
    simp [partitionSum]
  rw [← hsum]
  exact le_iSup₂_of_le 1 (![0, 1] : Fin 2 → I) (le_iSup_of_le hpart le_rfl)

/-- For a curve satisfying the distance law, the length (1.1.1) equals the endpoint distance. -/
theorem curveLength_eq_of_isGeodesicCurve {c : I → X} (hc : IsGeodesicCurve c) :
    curveLength c = edist (c 0) (c 1) := by
  refine le_antisymm ?_ (edist_le_curveLength c)
  refine iSup_le fun n => iSup_le fun t => iSup_le fun ht => ?_
  rw [partitionSum_eq_of_isGeodesicCurve hc t ht.1.monotone, ht.2.1, ht.2.2]
  simp [edist_dist]

/-- The distance law is inherited by every source restriction `c|[t₁,t₂]`. -/
theorem IsGeodesicCurve.curveRestrict {c : I → X} (hc : IsGeodesicCurve c) (t₁ t₂ : I) :
    IsGeodesicCurve (curveRestrict c t₁ t₂) := by
  intro s t
  simp only [KP.curveRestrict, Function.comp_apply, Set.Icc.convexComb_zero,
    Set.Icc.convexComb_one]
  rw [hc, hc t₁ t₂, Set.Icc.coe_convexComb, Set.Icc.coe_convexComb,
    show (1 - (s : ℝ)) * t₁ + s * t₂ - ((1 - t) * t₁ + t * t₂) = (s - t) * (t₂ - t₁) by ring,
    abs_mul, abs_sub_comm (t₂ : ℝ)]
  ring

/-- Source-length comparison: for a curve satisfying the distance law, the length of each
restriction `c|[t₁,t₂]` equals `d(c(t₁), c(t₂))`. -/
theorem curveLength_curveRestrict_of_isGeodesicCurve {c : I → X} (hc : IsGeodesicCurve c)
    (t₁ t₂ : I) : curveLength (curveRestrict c t₁ t₂) = edist (c t₁) (c t₂) := by
  rw [curveLength_eq_of_isGeodesicCurve (hc.curveRestrict t₁ t₂)]
  simp [KP.curveRestrict]

/-- The interior points `(0,1)` of the unit interval are dense in it. -/
theorem dense_Ioo_zero_one : Dense (Ioo (0 : I) 1) := by
  have h01 : (0 : I) ≠ 1 := fun h => by simpa using congrArg Subtype.val h
  rw [dense_iff_closure_eq, closure_Ioo h01]
  exact eq_univ_of_forall fun t => ⟨nonneg', le_one'⟩

/-- A literal KP Definition 1.1.2 geodesic satisfies the distance law on all of `[0,1]`
(the interior identities extend by continuity). -/
theorem IsSourceGeodesic.isGeodesicCurve {c : C(I, X)} (h : IsSourceGeodesic c) :
    IsGeodesicCurve c := by
  have hint : ∀ p : I × I, p ∈ Ioo (0 : I) 1 ×ˢ Ioo (0 : I) 1 →
      dist (c p.1) (c p.2) = dist (c 0) (c 1) * |(p.1 : ℝ) - p.2| := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    rcases lt_trichotomy s t with hst | rfl | hts
    · exact (h.2 s t hs.1 hst ht.2).2
    · simp
    · rw [dist_comm, abs_sub_comm]
      exact (h.2 t s ht.1 hts hs.2).2
  have hcont₁ : Continuous fun p : I × I => dist (c p.1) (c p.2) := by fun_prop
  have hcont₂ : Continuous fun p : I × I => dist (c 0) (c 1) * |(p.1 : ℝ) - p.2| := by
    fun_prop
  have heq := hcont₁.ext_on (dense_Ioo_zero_one.prod dense_Ioo_zero_one) hcont₂ hint
  intro s t
  exact congrFun heq (s, t)

/-- The literal KP Definition 1.1.2 geodesic condition is equivalent to the distance law. -/
theorem isSourceGeodesic_iff (c : C(I, X)) : IsSourceGeodesic c ↔ IsGeodesicCurve c := by
  refine ⟨fun h => h.isGeodesicCurve, fun hc => ⟨?_, fun t₁ t₂ _ _ _ => ⟨?_, hc t₁ t₂⟩⟩⟩
  · rw [IsRectifiable, curveLength_eq_of_isGeodesicCurve hc]
    exact edist_lt_top _ _
  · exact curveLength_curveRestrict_of_isGeodesicCurve hc t₁ t₂

/-! ### Geodesic segments -/

section Segments

variable {x y : X}

theorem isGeodesic_iff_isGeodesicCurve (γ : Path x y) : IsGeodesic γ ↔ IsGeodesicCurve γ := by
  simp only [IsGeodesic, IsGeodesicCurve, Path.source, Path.target]

/-- A path is a distance-law geodesic segment iff it is a KP Definition 1.1.2 geodesic. -/
theorem isGeodesic_iff_isSourceGeodesic (γ : Path x y) :
    IsGeodesic γ ↔ IsSourceGeodesic γ.toContinuousMap := by
  rw [isGeodesic_iff_isGeodesicCurve, isSourceGeodesic_iff]
  rfl

/-- Constant (zero-length) segments are geodesic. -/
theorem isGeodesic_refl (x : X) : IsGeodesic (Path.refl x) := by
  intro s t
  simp

namespace IsGeodesic

variable {γ : Path x y}

/-- Reversal of a geodesic segment is a geodesic segment. -/
theorem symm (h : IsGeodesic γ) : IsGeodesic γ.symm := by
  intro s t
  simp only [Path.symm_apply, Function.comp_apply]
  rw [h, coe_symm_eq, coe_symm_eq, dist_comm y x,
    show (1 - (s : ℝ)) - (1 - t) = t - s by ring, abs_sub_comm]

/-- Restriction (Mathlib's `Path.subpath`, which is the source `γ|[t₁,t₂]`) of a geodesic
segment is a geodesic segment. -/
theorem subpath (h : IsGeodesic γ) (t₁ t₂ : I) : IsGeodesic (γ.subpath t₁ t₂) :=
  (isGeodesic_iff_isGeodesicCurve _).mpr
    (((isGeodesic_iff_isGeodesicCurve γ).mp h).curveRestrict t₁ t₂)

theorem dist_source (h : IsGeodesic γ) (t : I) : dist x (γ t) = t * dist x y := by
  have := h 0 t
  rw [Path.source, Icc.coe_zero, zero_sub, abs_neg, abs_of_nonneg (nonneg t)] at this
  rw [this, mul_comm]

theorem dist_target (h : IsGeodesic γ) (t : I) : dist (γ t) y = (1 - t) * dist x y := by
  have := h t 1
  rw [Path.target, Icc.coe_one, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (le_one t))] at this
  rw [this, mul_comm]

/-- A geodesic segment has length (1.1.1) equal to the distance of its endpoints. -/
theorem curveLength_eq (h : IsGeodesic γ) : curveLength γ = edist x y := by
  rw [curveLength_eq_of_isGeodesicCurve ((isGeodesic_iff_isGeodesicCurve γ).mp h)]
  simp

/-- Every restriction of a geodesic segment has length equal to the distance of its endpoints. -/
theorem curveLength_subpath (h : IsGeodesic γ) (t₁ t₂ : I) :
    curveLength (γ.subpath t₁ t₂) = edist (γ t₁) (γ t₂) := by
  rw [(h.subpath t₁ t₂).curveLength_eq]

/-- A geodesic segment joining a point to itself is constant. -/
theorem eq_refl {γ : Path x x} (h : IsGeodesic γ) : γ = Path.refl x := by
  ext t
  have := h.dist_source t
  rw [dist_self, mul_zero, dist_eq_zero] at this
  simp [← this]

end IsGeodesic

end Segments

/-! ### Geodesic and uniquely geodesic spaces -/

theorem IsUniquelyGeodesicSpace.isGeodesicSpace (h : IsUniquelyGeodesicSpace X) :
    IsGeodesicSpace X :=
  fun x y => (h x y).exists

theorem isUniquelyGeodesicSpace_iff :
    IsUniquelyGeodesicSpace X ↔ IsGeodesicSpace X ∧
      ∀ (x y : X) (γ γ' : Path x y), IsGeodesic γ → IsGeodesic γ' → γ = γ' := by
  refine ⟨fun h => ⟨h.isGeodesicSpace, fun x y γ γ' hγ hγ' => (h x y).unique hγ hγ'⟩,
    fun h x y => ?_⟩
  obtain ⟨γ, hγ⟩ := h.1 x y
  exact ⟨γ, hγ, fun γ' hγ' => h.2 x y γ' γ hγ' hγ⟩

/-- `IsGeodesicSpace` agrees with KP Definition 1.1.4 stated with literal Definition 1.1.2
geodesics. -/
theorem isGeodesicSpace_iff_source :
    IsGeodesicSpace X ↔ ∀ x y : X, ∃ γ : Path x y, IsSourceGeodesic γ.toContinuousMap := by
  simp only [IsGeodesicSpace, isGeodesic_iff_isSourceGeodesic]

/-- `IsUniquelyGeodesicSpace` agrees with KP Definition 1.1.4 stated with literal
Definition 1.1.2 geodesics. -/
theorem isUniquelyGeodesicSpace_iff_source :
    IsUniquelyGeodesicSpace X ↔
      ∀ x y : X, ∃! γ : Path x y, IsSourceGeodesic γ.toContinuousMap := by
  simp only [IsUniquelyGeodesicSpace, isGeodesic_iff_isSourceGeodesic]

/-! ### Nonpositive curvature -/

/-- The inequality of KP Definition 1.1.8 for the pair `x, y` and the candidate point `m`:
for every `z`, `d(x,z)² + d(y,z)² ≥ 2 d(m,z)² + (1/2) d(x,y)²`. -/
def IsNPCMidpoint (x y m : X) : Prop :=
  ∀ z : X, 2 * dist m z ^ 2 + (1 / 2) * dist x y ^ 2 ≤ dist x z ^ 2 + dist y z ^ 2

variable (X) in
/-- KP Definition 1.1.8: a metric space is non-positively curved if for every `x, y` there is
`m` such that for all `z`, `d(x,z)² + d(y,z)² ≥ 2 d(m,z)² + (1/2) d(x,y)²`. No completeness,
geodesic existence or uniqueness is part of this predicate. -/
def IsNonpositivelyCurved : Prop :=
  ∀ x y : X, ∃ m : X, IsNPCMidpoint x y m

namespace IsNPCMidpoint

variable {x y m : X}

theorem dist_left_le (h : IsNPCMidpoint x y m) : dist x m ≤ dist x y / 2 := by
  have hz := h x
  rw [dist_self, dist_comm y x, dist_comm m x] at hz
  nlinarith [dist_nonneg (x := x) (y := m), dist_nonneg (x := x) (y := y)]

theorem dist_right_le (h : IsNPCMidpoint x y m) : dist y m ≤ dist x y / 2 := by
  have hz := h y
  rw [dist_self, dist_comm m y] at hz
  nlinarith [dist_nonneg (x := y) (y := m), dist_nonneg (x := x) (y := y)]

/-- A point satisfying the KP Definition 1.1.8 inequality for `x, y` is a metric midpoint. -/
theorem dist_left (h : IsNPCMidpoint x y m) : dist x m = dist x y / 2 := by
  have h₁ := h.dist_left_le
  have h₂ := h.dist_right_le
  have h₃ := dist_triangle x m y
  rw [dist_comm m y] at h₃
  linarith

/-- A point satisfying the KP Definition 1.1.8 inequality for `x, y` is a metric midpoint. -/
theorem dist_right (h : IsNPCMidpoint x y m) : dist y m = dist x y / 2 := by
  have h₁ := h.dist_left_le
  have h₂ := h.dist_right_le
  have h₃ := dist_triangle x m y
  rw [dist_comm m y] at h₃
  linarith

end IsNPCMidpoint

/-! ### Bounded sets, joint diameter, radius and barycenters -/

/-- KP Definition 1.1.1(1) compared with Mathlib boundedness: in a nonempty metric space, a set
is bounded iff it lies in some open ball `B(x, r)` with `r > 0`. -/
theorem isBounded_iff_subset_ball_pos [Nonempty X] (A : Set X) :
    IsBounded A ↔ ∃ x : X, ∃ r : ℝ, 0 < r ∧ A ⊆ Metric.ball x r := by
  refine ⟨fun hA => ?_, fun ⟨x, r, _, hA⟩ => Metric.isBounded_ball.subset hA⟩
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball x).mp hA
  exact ⟨x, max r 1, lt_max_of_lt_right one_pos,
    hr.trans (Metric.ball_subset_ball (le_max_left r 1))⟩

/-- KP Definition 1.1.1(2): the joint diameter `diam(A, B) = sup {d(a, b) | a ∈ A, b ∈ B}`,
valued in `[0, ∞]`. The source uses it for nonempty `A, B`; for an empty argument this
supremum is `0`. -/
def jointDiam (A B : Set X) : ℝ≥0∞ :=
  ⨆ (a ∈ A) (b ∈ B), edist a b

/-- KP Definition 1.1.1(3): `diam(A) = diam(A, A)` is Mathlib's extended diameter. -/
theorem jointDiam_self (A : Set X) : jointDiam A A = Metric.ediam A :=
  rfl

theorem jointDiam_singleton_left (x : X) (M : Set X) :
    jointDiam {x} M = ⨆ m ∈ M, edist x m := by
  simp [jointDiam]

theorem edist_le_jointDiam_singleton {x m : X} {M : Set X} (hm : m ∈ M) :
    edist x m ≤ jointDiam {x} M := by
  rw [jointDiam_singleton_left]
  exact le_iSup₂_of_le m hm le_rfl

/-- `diam(x, M)` is finite iff `M` is bounded. -/
theorem jointDiam_singleton_ne_top_iff (x : X) (M : Set X) :
    jointDiam {x} M ≠ ⊤ ↔ IsBounded M := by
  constructor
  · intro h
    refine (Metric.isBounded_iff_subset_closedBall x).mpr ⟨(jointDiam {x} M).toReal, ?_⟩
    intro m hm
    rw [Metric.mem_closedBall, dist_comm, dist_edist]
    exact ENNReal.toReal_mono h (edist_le_jointDiam_singleton hm)
  · intro hM
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall x).mp hM
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := r)) ?_
    rw [jointDiam_singleton_left]
    refine iSup₂_le fun m hm => ?_
    rw [edist_dist, dist_comm]
    exact ENNReal.ofReal_le_ofReal (hr hm)

/-- For a nonempty bounded `M`, the real number `diam(x, M)` is the genuine least upper bound of
the distances `d(x, m)`, `m ∈ M`. -/
theorem isLUB_toReal_jointDiam_singleton (x : X) {M : Set X} (hne : M.Nonempty)
    (hM : IsBounded M) : IsLUB (dist x '' M) (jointDiam {x} M).toReal := by
  have hfin := (jointDiam_singleton_ne_top_iff x M).mpr hM
  refine ⟨?_, fun r hr => ?_⟩
  · rintro _ ⟨m, hm, rfl⟩
    rw [dist_edist]
    exact ENNReal.toReal_mono hfin (edist_le_jointDiam_singleton hm)
  · obtain ⟨m₀, hm₀⟩ := hne
    have hr0 : 0 ≤ r := dist_nonneg.trans (hr ⟨m₀, hm₀, rfl⟩)
    refine ENNReal.toReal_le_of_le_ofReal hr0 ?_
    rw [jointDiam_singleton_left]
    refine iSup₂_le fun m hm => ?_
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (hr ⟨m, hm, rfl⟩)

/-- KP Definition 1.1.12(2): the radius `r(M) = inf {diam(x, M) | x ∈ M}` (centers `x` range
over `M`), valued in `[0, ∞]`. The source states it for convex `M`; the formula does not use
convexity, and it is `⊤` for empty or unbounded `M`. -/
def radius (M : Set X) : ℝ≥0∞ :=
  ⨅ x ∈ M, jointDiam {x} M

/-- KP Definition 1.1.12(3): a barycenter of `M` is a point `x ∈ M` with `diam(x, M) = r(M)`. -/
def IsBarycenter (M : Set X) (b : X) : Prop :=
  b ∈ M ∧ jointDiam {b} M = radius M

theorem radius_le_jointDiam_singleton {M : Set X} {x : X} (hx : x ∈ M) :
    radius M ≤ jointDiam {x} M :=
  iInf₂_le x hx

theorem radius_empty : radius (∅ : Set X) = ⊤ := by
  simp [radius]

/-- For nonempty `M`, the radius is finite iff `M` is bounded. -/
theorem radius_ne_top_iff {M : Set X} (hne : M.Nonempty) : radius M ≠ ⊤ ↔ IsBounded M := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := hne
    by_contra hM
    exact h (top_le_iff.mp (le_iInf₂ fun y _ =>
      top_le_iff.mpr (not_not.mp (mt (jointDiam_singleton_ne_top_iff y M).mp hM))))
  · intro hM
    obtain ⟨x, hx⟩ := hne
    exact ne_top_of_le_ne_top ((jointDiam_singleton_ne_top_iff x M).mpr hM)
      (radius_le_jointDiam_singleton hx)

/-- The radius of an unbounded set is `⊤`; no totalized real value is used. -/
theorem radius_eq_top_of_not_isBounded {M : Set X} (hM : ¬IsBounded M) : radius M = ⊤ := by
  rcases M.eq_empty_or_nonempty with rfl | hne
  · exact radius_empty
  · by_contra h
    exact hM ((radius_ne_top_iff hne).mp h)

/-- For a nonempty bounded `M`, the real number `r(M)` is the genuine greatest lower bound of the
real numbers `diam(x, M)`, `x ∈ M`. -/
theorem isGLB_toReal_radius {M : Set X} (hne : M.Nonempty) (hM : IsBounded M) :
    IsGLB ((fun x => (jointDiam {x} M).toReal) '' M) (radius M).toReal := by
  have hfin : radius M ≠ ⊤ := (radius_ne_top_iff hne).mpr hM
  refine ⟨?_, fun r hr => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ENNReal.toReal_mono ((jointDiam_singleton_ne_top_iff x M).mpr hM)
      (radius_le_jointDiam_singleton hx)
  · rcases le_or_gt r 0 with hr0 | hr0
    · exact hr0.trans ENNReal.toReal_nonneg
    · have hle : ENNReal.ofReal r ≤ radius M := by
        refine le_iInf₂ fun x hx => ?_
        have hx' : r ≤ (jointDiam {x} M).toReal := hr ⟨x, hx, rfl⟩
        rw [← ENNReal.ofReal_toReal ((jointDiam_singleton_ne_top_iff x M).mpr hM)]
        exact ENNReal.ofReal_le_ofReal hx'
      calc r = (ENNReal.ofReal r).toReal := (ENNReal.toReal_ofReal hr0.le).symm
        _ ≤ (radius M).toReal := ENNReal.toReal_mono hfin hle

/-- For a bounded set, the barycenter condition can be read in real numbers. -/
theorem isBarycenter_iff_toReal {M : Set X} (hM : IsBounded M) {b : X} :
    IsBarycenter M b ↔ b ∈ M ∧ (jointDiam {b} M).toReal = (radius M).toReal := by
  refine and_congr_right fun hb => ?_
  have hne : M.Nonempty := ⟨b, hb⟩
  exact (ENNReal.toReal_eq_toReal_iff' ((jointDiam_singleton_ne_top_iff b M).mpr hM)
    ((radius_ne_top_iff hne).mpr hM)).symm

/-- In the degenerate unbounded case every point of `M` is a barycenter, both values being `⊤`;
the source's barycenter theorem (Theorem 1.1.15) concerns bounded sets only. -/
theorem isBarycenter_of_not_isBounded {M : Set X} (hM : ¬IsBounded M) {b : X} (hb : b ∈ M) :
    IsBarycenter M b := by
  refine ⟨hb, ?_⟩
  rw [radius_eq_top_of_not_isBounded hM]
  by_contra h
  exact hM ((jointDiam_singleton_ne_top_iff b M).mp h)

/-! ### Convex sets -/

/-- Carrier-only predicate: `M` contains the image of every geodesic segment joining two of its
points. This holds for the empty set; it is *not* the source notion of convexity. -/
def ContainsGeodesics (M : Set X) : Prop :=
  ∀ ⦃x : X⦄, x ∈ M → ∀ ⦃y : X⦄, y ∈ M → ∀ γ : Path x y, IsGeodesic γ → range γ ⊆ M

/-- Corrected KP Definition 1.1.12(1), all-segments form: a *nonempty* set containing every
geodesic segment between its points. Over a uniquely geodesic space this is the source
definition, see `isSourceConvex_iff`. -/
def IsGeodesicallyConvex (M : Set X) : Prop :=
  M.Nonempty ∧ ContainsGeodesics M

/-- The unique geodesic joining `x` and `y` in a uniquely geodesic space. -/
def uniqueGeodesic (hX : IsUniquelyGeodesicSpace X) (x y : X) : Path x y :=
  (hX x y).exists.choose

theorem isGeodesic_uniqueGeodesic (hX : IsUniquelyGeodesicSpace X) (x y : X) :
    IsGeodesic (uniqueGeodesic hX x y) :=
  (hX x y).exists.choose_spec

theorem eq_uniqueGeodesic (hX : IsUniquelyGeodesicSpace X) {x y : X} {γ : Path x y}
    (hγ : IsGeodesic γ) : γ = uniqueGeodesic hX x y :=
  (hX x y).unique hγ (isGeodesic_uniqueGeodesic hX x y)

/-- Corrected KP Definition 1.1.12(1), literally: in a uniquely geodesic space, a nonempty set
`M` is convex if for `x, y ∈ M` the image of the unique geodesic joining them lies in `M`. -/
def IsSourceConvex (hX : IsUniquelyGeodesicSpace X) (M : Set X) : Prop :=
  M.Nonempty ∧ ∀ x ∈ M, ∀ y ∈ M, range (uniqueGeodesic hX x y) ⊆ M

/-- Over a uniquely geodesic space the literal source convexity is the all-segments form. -/
theorem isSourceConvex_iff (hX : IsUniquelyGeodesicSpace X) (M : Set X) :
    IsSourceConvex hX M ↔ IsGeodesicallyConvex M := by
  refine and_congr_right fun _ => ⟨fun h x hx y hy γ hγ => ?_, fun h x hx y hy =>
    h hx hy _ (isGeodesic_uniqueGeodesic hX x y)⟩
  rw [eq_uniqueGeodesic hX hγ]
  exact h x hx y hy

theorem containsGeodesics_empty : ContainsGeodesics (∅ : Set X) :=
  fun _ hx => hx.elim

/-- Regression for the correction of KP Definition 1.1.12(1): the empty set is not convex. -/
theorem not_isGeodesicallyConvex_empty : ¬IsGeodesicallyConvex (∅ : Set X) :=
  fun h => h.1.ne_empty rfl

theorem not_isSourceConvex_empty (hX : IsUniquelyGeodesicSpace X) :
    ¬IsSourceConvex hX (∅ : Set X) :=
  fun h => h.1.ne_empty rfl

theorem containsGeodesics_univ : ContainsGeodesics (univ : Set X) :=
  fun _ _ _ _ _ _ => subset_univ _

theorem isGeodesicallyConvex_univ [Nonempty X] : IsGeodesicallyConvex (univ : Set X) :=
  ⟨univ_nonempty, containsGeodesics_univ⟩

theorem isGeodesicallyConvex_singleton (x : X) : IsGeodesicallyConvex ({x} : Set X) := by
  refine ⟨singleton_nonempty x, ?_⟩
  intro a ha b hb γ hγ
  rw [mem_singleton_iff] at ha hb
  subst ha hb
  rw [hγ.eq_refl, Path.refl_range]

theorem ContainsGeodesics.sInter {S : Set (Set X)} (h : ∀ C ∈ S, ContainsGeodesics C) :
    ContainsGeodesics (⋂₀ S) :=
  fun _ hx _ hy γ hγ => subset_sInter fun C hC => h C hC (hx C hC) (hy C hC) γ hγ

theorem ContainsGeodesics.inter {M N : Set X} (hM : ContainsGeodesics M)
    (hN : ContainsGeodesics N) : ContainsGeodesics (M ∩ N) :=
  fun _ hx _ hy γ hγ => subset_inter (hM hx.1 hy.1 γ hγ) (hN hx.2 hy.2 γ hγ)

theorem IsGeodesicallyConvex.apply_mem {M : Set X} (hM : IsGeodesicallyConvex M) {x y : X}
    (hx : x ∈ M) (hy : y ∈ M) {γ : Path x y} (hγ : IsGeodesic γ) (t : I) : γ t ∈ M :=
  hM.2 hx hy γ hγ (mem_range_self t)

/-! ### Closed convex hull -/

/-- KP Definition 1.1.14: the closed convex hull of `M`, the intersection of all closed bounded
convex subsets of `X` containing `M`. The (corrected) source discussion takes `X` a
non-positively curved geodesic space and `M` nonempty and bounded; there Lemma 1.1.13 (not proved
here) provides a closed bounded convex set containing `M`. As a set the intersection is defined
unconditionally; it is `univ` if no such set exists. -/
def closedGeodesicConvexHull (M : Set X) : Set X :=
  ⋂₀ {C : Set X | IsClosed C ∧ IsBounded C ∧ IsGeodesicallyConvex C ∧ M ⊆ C}

theorem subset_closedGeodesicConvexHull (M : Set X) : M ⊆ closedGeodesicConvexHull M :=
  subset_sInter fun _ hC => hC.2.2.2

theorem isClosed_closedGeodesicConvexHull (M : Set X) : IsClosed (closedGeodesicConvexHull M) :=
  isClosed_sInter fun _ hC => hC.1

/-- The closed convex hull is contained in every closed bounded convex set containing `M`. -/
theorem closedGeodesicConvexHull_subset {M C : Set X} (hC : IsClosed C) (hb : IsBounded C)
    (hc : IsGeodesicallyConvex C) (hMC : M ⊆ C) : closedGeodesicConvexHull M ⊆ C :=
  sInter_subset_of_mem ⟨hC, hb, hc, hMC⟩

theorem containsGeodesics_closedGeodesicConvexHull (M : Set X) :
    ContainsGeodesics (closedGeodesicConvexHull M) :=
  ContainsGeodesics.sInter fun _ hC => hC.2.2.1.2

theorem isGeodesicallyConvex_closedGeodesicConvexHull {M : Set X} (hM : M.Nonempty) :
    IsGeodesicallyConvex (closedGeodesicConvexHull M) :=
  ⟨hM.mono (subset_closedGeodesicConvexHull M), containsGeodesics_closedGeodesicConvexHull M⟩

/-- Given one closed bounded convex set containing `M` (which KP obtain from Lemma 1.1.13), the
closed convex hull is bounded. -/
theorem isBounded_closedGeodesicConvexHull {M : Set X}
    (h : ∃ C : Set X, IsClosed C ∧ IsBounded C ∧ IsGeodesicallyConvex C ∧ M ⊆ C) :
    IsBounded (closedGeodesicConvexHull M) := by
  obtain ⟨C, hC, hb, hc, hMC⟩ := h
  exact hb.subset (closedGeodesicConvexHull_subset hC hb hc hMC)

/-! ### Bounded actions -/

section BoundedAction

variable {G : Type*} [SMul G X]

variable (X) in
/-- KP Definition 1.1.18, through condition (2) of Lemma 1.1.17: the set `A` of transformations
of `X` (given by an action of `G`) has bounded action if some orbit `{g • x | g ∈ A}` is
bounded. The source applies this to sets of isometries, i.e. under `IsIsometricSMul G X`. -/
def HasBoundedAction (A : Set G) : Prop :=
  ∃ x : X, IsBounded ((fun g : G => g • x) '' A)

/-- KP Lemma 1.1.17: for isometries of a nonempty metric space, one orbit is bounded iff every
orbit is bounded. -/
theorem hasBoundedAction_iff_forall [IsIsometricSMul G X] [Nonempty X] (A : Set G) :
    HasBoundedAction X A ↔ ∀ x : X, IsBounded ((fun g : G => g • x) '' A) := by
  refine ⟨fun ⟨x₀, hx₀⟩ y => ?_, fun h => ⟨Classical.arbitrary X, h _⟩⟩
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall x₀).mp hx₀
  refine (Metric.isBounded_iff_subset_closedBall x₀).mpr ⟨dist y x₀ + R, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  have hgx : dist (g • x₀) x₀ ≤ R := hR ⟨g, hg, rfl⟩
  rw [Metric.mem_closedBall]
  calc dist (g • y) x₀ ≤ dist (g • y) (g • x₀) + dist (g • x₀) x₀ := dist_triangle _ _ _
    _ = dist y x₀ + dist (g • x₀) x₀ := by rw [dist_smul]
    _ ≤ dist y x₀ + R := by linarith

end BoundedAction

/-- The tautological action `f • x = f x` of the isometry group `X ≃ᵢ X` on `X`. It is scoped to
this namespace; it lets KP's literal "sets of isometries of `X`" be used with
`HasBoundedAction` and with Mathlib's stabilizer and fixed-point API. -/
scoped instance isometryEquivMulAction : MulAction (X ≃ᵢ X) X where
  smul f x := f x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem isometryEquiv_smul_def (f : X ≃ᵢ X) (x : X) : f • x = f x :=
  rfl

scoped instance isometryEquivIsIsometricSMul : IsIsometricSMul (X ≃ᵢ X) X :=
  ⟨fun f => f.isometry⟩

/-- KP Definition 1.1.18 for a literal set `A` of isometries of `X`. -/
theorem hasBoundedAction_isometryEquiv_iff (A : Set (X ≃ᵢ X)) :
    HasBoundedAction X A ↔ ∃ x : X, IsBounded ((fun f : X ≃ᵢ X => f x) '' A) :=
  Iff.rfl

/-! ### Elementary examples: real inner product spaces -/

section Examples

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The straight segment `t ↦ (1 - t) x + t y` is a geodesic segment in a real normed space. -/
theorem isGeodesic_segment {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (x y : V) :
    IsGeodesic (Path.segment x y) := by
  intro s t
  rw [Path.segment_apply, Path.segment_apply, dist_lineMap_lineMap, Real.dist_eq, mul_comm]

theorem isGeodesicSpace_of_normedSpace (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    IsGeodesicSpace V :=
  fun x y => ⟨Path.segment x y, isGeodesic_segment x y⟩

/-- In a strictly convex real normed space every geodesic segment is the straight segment. -/
theorem IsGeodesic.eq_segment {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [StrictConvexSpace ℝ V] {x y : V} {γ : Path x y} (hγ : IsGeodesic γ) :
    γ = Path.segment x y := by
  ext t
  rw [Path.segment_apply]
  have hsum : dist x (γ t) + dist (γ t) y = dist x y := by
    rw [hγ.dist_source, hγ.dist_target]
    ring
  obtain ⟨s, ⟨hs0, hs1⟩, hst⟩ := (dist_add_dist_eq_iff (V := V)).mp hsum
  rcases eq_or_ne x y with rfl | hxy
  · have := hγ.dist_source t
    rw [dist_self, mul_zero, dist_eq_zero] at this
    rw [AffineMap.lineMap_same_apply, ← this]
  · have hd : dist x (γ t) = s * dist x y := by
      rw [← hst, dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg hs0]
    rw [hγ.dist_source] at hd
    have hst' : (t : ℝ) = s := mul_right_cancel₀ (dist_ne_zero.mpr hxy) hd
    rw [hst', hst]

theorem isUniquelyGeodesicSpace_of_strictConvexSpace (V : Type*) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [StrictConvexSpace ℝ V] : IsUniquelyGeodesicSpace V :=
  fun x y => ⟨Path.segment x y, isGeodesic_segment x y, fun _ hγ => hγ.eq_segment⟩

/-- In a real inner product space the midpoint `(x + y)/2` satisfies the inequality of
KP Definition 1.1.8 with equality (the parallelogram law, KP Remark 1.1.9). -/
theorem isNPCMidpoint_smul_add (x y : E) : IsNPCMidpoint x y ((1 / 2 : ℝ) • (x + y)) := by
  intro z
  set u := x - z
  set v := y - z
  have hm : (1 / 2 : ℝ) • (x + y) - z = (1 / 2 : ℝ) • (u + v) := by
    simp only [u, v]
    module
  have hxy : x - y = u - v := by
    simp only [u, v]
    abel
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, dist_eq_norm, hm, hxy, norm_smul,
    Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hp := parallelogram_law_with_norm ℝ u v
  nlinarith [hp]

theorem isNonpositivelyCurved_of_innerProductSpace : IsNonpositivelyCurved E :=
  fun x y => ⟨(1 / 2 : ℝ) • (x + y), isNPCMidpoint_smul_add x y⟩

/-- The real line is a uniquely geodesic, non-positively curved metric space. -/
theorem real_isGeodesicSpace_isUniquelyGeodesicSpace_isNonpositivelyCurved :
    IsGeodesicSpace ℝ ∧ IsUniquelyGeodesicSpace ℝ ∧ IsNonpositivelyCurved ℝ :=
  ⟨isGeodesicSpace_of_normedSpace ℝ, isUniquelyGeodesicSpace_of_strictConvexSpace ℝ,
    isNonpositivelyCurved_of_innerProductSpace⟩

end Examples

end Langlands.Geometry.Metric.KP
