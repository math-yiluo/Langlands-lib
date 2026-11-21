import Langlands.Geometry.Analytic.DrinfeldFacetSpaces
import Langlands.Geometry.Analytic.DrinfeldBuildingCovering

/-! # Nearest vertices in the building of `PGL(V)` over a local field -/

noncomputable section

universe v w

namespace Langlands.Analytic

open Set
open scoped ENNReal

namespace VectorNorm

/-! ## The absolute value of a local field is discrete -/

section Discrete

variable {F : Type v} [NontriviallyNormedField F] [IsUltrametricDist F]

/-- `ϖ` has the largest absolute value below `1` (it is a uniformizer). -/
def IsMaxBelowOne (ϖ : F) : Prop := 0 < ‖ϖ‖ ∧ ‖ϖ‖ < 1 ∧ ∀ t : F, ‖t‖ < 1 → ‖t‖ ≤ ‖ϖ‖

/-- Over a locally compact non-Archimedean field, the absolute values below `1` have a largest
element. -/
theorem exists_isMaxBelowOne [ProperSpace F] : ∃ ϖ : F, IsMaxBelowOne ϖ := by
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one F
  set A : Set F := {t | ‖c‖ ≤ ‖t‖ ∧ ‖t‖ ≤ 1} with hA_def
  have hA : IsCompact A := by
    refine (isCompact_closedBall (0 : F) 1).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · intro t ht
      simpa [Metric.mem_closedBall, dist_zero_right] using ht.2
  have hfin : (norm '' A).Finite := by
    obtain ⟨T, hTA, hT⟩ := hA.elim_nhds_subcover (fun t => Metric.ball t ‖t‖)
      (fun t ht => Metric.ball_mem_nhds t (lt_of_lt_of_le hc0 ht.1))
    refine (T.finite_toSet.image norm).subset ?_
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨t, htT, hst⟩ := mem_iUnion₂.1 (hT hs)
    refine ⟨t, htT, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hst
    have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hst)
    rw [add_sub_cancel] at h
    rw [h, max_eq_left hst.le]
  set B : Set ℝ := norm '' A ∩ Iio 1
  have hBfin : B.Finite := hfin.subset inter_subset_left
  have hBne : B.Nonempty := ⟨‖c‖, ⟨c, ⟨le_rfl, hc1.le⟩, rfl⟩, hc1⟩
  obtain ⟨m, hmB, hmax⟩ := Set.exists_max_image B id hBfin hBne
  obtain ⟨⟨ϖ, hϖA, rfl⟩, hϖ1⟩ := hmB
  refine ⟨ϖ, lt_of_lt_of_le hc0 hϖA.1, hϖ1, fun t ht => ?_⟩
  by_cases htc : ‖c‖ ≤ ‖t‖
  · exact hmax ‖t‖ ⟨⟨t, ⟨htc, ht.le⟩, rfl⟩, ht⟩
  · push Not at htc
    exact (htc.trans_le hϖA.1).le

variable {ϖ : F} (hϖ : IsMaxBelowOne ϖ)
include hϖ

omit [IsUltrametricDist F] in
theorem IsMaxBelowOne.one_lt_inv : 1 < ‖ϖ‖⁻¹ :=
  (one_lt_inv₀ hϖ.1).2 hϖ.2.1

omit [IsUltrametricDist F] in
theorem IsMaxBelowOne.norm_eq_one {u : F} (h₁ : ‖ϖ‖ < ‖u‖) (h₂ : ‖u‖ < ‖ϖ‖⁻¹) : ‖u‖ = 1 := by
  have hu : u ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h₁
    exact absurd hϖ.1 (not_lt.2 h₁.le)
  rcases lt_trichotomy ‖u‖ 1 with h | h | h
  · exact absurd (hϖ.2.2 u h) (not_le.2 h₁)
  · exact h
  · have h' : ‖u⁻¹‖ < 1 := by
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ h
    have h'' := hϖ.2.2 _ h'
    rw [norm_inv] at h''
    exact absurd (inv_le_of_inv_le₀ (norm_pos_iff.2 hu) h'') (not_le.2 h₂)

omit [IsUltrametricDist F] in
/-- Every nonzero absolute value is an integral power of `q = ‖ϖ‖⁻¹`. -/
theorem IsMaxBelowOne.exists_norm_eq_zpow {t : F} (ht : t ≠ 0) :
    ∃ n : ℤ, ‖t‖ = ‖ϖ‖⁻¹ ^ n := by
  obtain ⟨n, hn₁, hn₂⟩ := exists_mem_Ico_zpow (norm_pos_iff.2 ht) hϖ.one_lt_inv
  refine ⟨n, ?_⟩
  have hq : 0 < ‖ϖ‖⁻¹ := inv_pos.2 hϖ.1
  have hu : ‖t * ϖ ^ n‖ = ‖t‖ / ‖ϖ‖⁻¹ ^ n := by
    rw [norm_mul, norm_zpow, inv_zpow, div_inv_eq_mul]
  have h1 : ‖ϖ‖ < ‖t * ϖ ^ n‖ := by
    rw [hu, lt_div_iff₀ (zpow_pos hq n)]
    calc ‖ϖ‖ * ‖ϖ‖⁻¹ ^ n < 1 * ‖ϖ‖⁻¹ ^ n :=
          mul_lt_mul_of_pos_right hϖ.2.1 (zpow_pos hq n)
      _ ≤ ‖t‖ := by rw [one_mul]; exact hn₁
  have h2 : ‖t * ϖ ^ n‖ < ‖ϖ‖⁻¹ := by
    rw [hu, div_lt_iff₀ (zpow_pos hq n), ← zpow_one_add₀ hq.ne', add_comm]
    exact hn₂
  have := hϖ.norm_eq_one h1 h2
  rw [hu, div_eq_one_iff_eq (zpow_pos hq n).ne'] at this
  exact this

end Discrete

/-! ## Rounding up to an integral power of `q` -/

section Up

/-- For `q > 1` and `r > 0`, the least integral power `q ^ n` with `r ≤ q ^ n`. -/
def up (q r : ℝ) : ℝ :=
  if h : 0 < r ∧ 1 < q then q ^ (Classical.choose (exists_mem_Ioc_zpow h.1 h.2) + 1) else 0

theorem up_of_nonpos {q r : ℝ} (hr : r ≤ 0) : up q r = 0 := by
  unfold up
  split_ifs with h
  · exact absurd hr (not_le.2 h.1)
  · rfl

theorem up_nonneg {q r : ℝ} : 0 ≤ up q r := by
  unfold up
  split_ifs with h
  · exact (zpow_pos (zero_lt_one.trans h.2) _).le
  · exact le_rfl

variable {q : ℝ} (hq : 1 < q)
include hq

theorem up_spec {r : ℝ} (hr : 0 < r) :
    ∃ n : ℤ, up q r = q ^ n ∧ r ≤ q ^ n ∧ q ^ n < q * r := by
  have h : 0 < r ∧ 1 < q := ⟨hr, hq⟩
  have hn := Classical.choose_spec (exists_mem_Ioc_zpow h.1 h.2)
  refine ⟨Classical.choose (exists_mem_Ioc_zpow h.1 h.2) + 1, ?_, hn.2, ?_⟩
  · unfold up
    split_ifs
    rfl
  rw [zpow_add_one₀ (by linarith), mul_comm]
  exact mul_lt_mul_of_pos_left hn.1 (by linarith)

theorem up_eq_of {r : ℝ} {n : ℤ} (hr : 0 < r) (h₁ : r ≤ q ^ n) (h₂ : q ^ n < q * r) :
    up q r = q ^ n := by
  obtain ⟨m, hm, hm₁, hm₂⟩ := up_spec hq hr
  rw [hm]
  have hq0 : 0 < q := by linarith
  rcases lt_trichotomy m n with h | h | h
  · exfalso
    have h3 : q ^ (m + 1) ≤ q ^ n := zpow_le_zpow_right₀ hq.le (by omega)
    rw [zpow_add_one₀ hq0.ne', mul_comm] at h3
    have h4 : q * r ≤ q * q ^ m := mul_le_mul_of_nonneg_left hm₁ hq0.le
    linarith
  · rw [h]
  · exfalso
    have h3 : q ^ (n + 1) ≤ q ^ m := zpow_le_zpow_right₀ hq.le (by omega)
    rw [zpow_add_one₀ hq0.ne', mul_comm] at h3
    have h4 : q * r ≤ q * q ^ n := mul_le_mul_of_nonneg_left h₁ hq0.le
    linarith

theorem up_pos {r : ℝ} (hr : 0 < r) : 0 < up q r := by
  obtain ⟨n, hn, -, -⟩ := up_spec hq hr
  rw [hn]
  exact zpow_pos (by linarith) n

theorem le_up {r : ℝ} (hr : 0 < r) : r ≤ up q r := by
  obtain ⟨n, hn, h, -⟩ := up_spec hq hr
  rw [hn]
  exact h

theorem up_lt {r : ℝ} (hr : 0 < r) : up q r < q * r := by
  obtain ⟨n, hn, -, h⟩ := up_spec hq hr
  rw [hn]
  exact h

theorem up_mono {r r' : ℝ} (hr : 0 < r) (h : r ≤ r') : up q r ≤ up q r' := by
  obtain ⟨m, hm, hm₁, hm₂⟩ := up_spec hq hr
  obtain ⟨m', hm', hm₁', hm₂'⟩ := up_spec hq (hr.trans_le h)
  rw [hm, hm']
  by_contra hlt
  push Not at hlt
  have hmm : m' < m := (zpow_lt_zpow_iff_right₀ hq).1 hlt
  have h3 : q ^ (m' + 1) ≤ q ^ m := zpow_le_zpow_right₀ hq.le (by omega)
  rw [zpow_add_one₀ (by linarith), mul_comm] at h3
  have h1 : q * r ≤ q * q ^ m' := mul_le_mul_of_nonneg_left (h.trans hm₁') (by linarith)
  linarith

theorem up_zpow_mul (k : ℤ) {r : ℝ} (hr : 0 < r) : up q (q ^ k * r) = q ^ k * up q r := by
  have hq0 : 0 < q := by linarith
  obtain ⟨m, hm, hm₁, hm₂⟩ := up_spec hq hr
  rw [hm, ← zpow_add₀ hq0.ne']
  refine up_eq_of hq (mul_pos (zpow_pos hq0 k) hr) ?_ ?_
  · rw [zpow_add₀ hq0.ne']
    exact mul_le_mul_of_nonneg_left hm₁ (zpow_pos hq0 k).le
  · rw [zpow_add₀ hq0.ne', mul_left_comm]
    exact mul_lt_mul_of_pos_left hm₂ (zpow_pos hq0 k)

end Up

/-! ## Elementary properties of ultrametric norms -/

section Basic

variable {F : Type v} [NormedField F] {V : Type w} [AddCommGroup V] [Module F V]
  (ν : VectorNorm F V)

theorem apply_add_eq_of_lt {a b : V} (h : ν b < ν a) : ν (a + b) = ν a := by
  apply le_antisymm
  · exact (ν.add_le_max a b).trans (max_le le_rfl h.le)
  · have h1 := ν.add_le_max (a + b) (-b)
    rw [add_neg_cancel_right, apply_neg] at h1
    rcases le_max_iff.1 h1 with h2 | h2
    · exact h2
    · exact absurd h2 (not_le.2 h)

theorem apply_sum_lt {ι : Type*} (s : Finset ι) (x : ι → V) {C : ℝ} (hC : 0 < C)
    (h : ∀ i ∈ s, ν (x i) < C) : ν (∑ i ∈ s, x i) < C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (ν.add_le_max _ _).trans_lt (max_lt (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj)))

end Basic

/-! ## Norms in one interval `[c, q c)` -/

section Independence

variable {F : Type v} [NontriviallyNormedField F] {ϖ : F}
  {V : Type w} [AddCommGroup V] [Module F V] (ν : VectorNorm F V)

/-- Vectors whose norms are pairwise distinct and lie in one interval `[c, q c)` are linearly
independent. -/
theorem linearIndependent_of_values (hϖ : IsMaxBelowOne ϖ) {ι : Type*} [Fintype ι]
    (b : ι → V) {c : ℝ} (hc : 0 < c) (hb : ∀ i, c ≤ ν (b i) ∧ ν (b i) < ‖ϖ‖⁻¹ * c)
    (hinj : Function.Injective fun i => ν (b i)) : LinearIndependent F b := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push Not at hne
  set T := Finset.univ.filter fun i => g i ≠ 0 with hT_def
  have hT : T.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, by simp [T, hi]⟩
  obtain ⟨i₀, hi₀T, hmax⟩ := T.exists_max_image (fun i => ν (g i • b i)) hT
  have hi₀ : g i₀ ≠ 0 := (Finset.mem_filter.1 hi₀T).2
  have hbpos : ∀ i, 0 < ν (b i) := fun i => hc.trans_le (hb i).1
  have hpos : 0 < ν (g i₀ • b i₀) := by
    rw [ν.map_smul]
    exact mul_pos (norm_pos_iff.2 hi₀) (hbpos i₀)
  have hlt : ∀ j ∈ Finset.univ.erase i₀, ν (g j • b j) < ν (g i₀ • b i₀) := by
    intro j hj
    have hji : j ≠ i₀ := Finset.ne_of_mem_erase hj
    by_cases hgj : g j = 0
    · rw [hgj, zero_smul, map_zero]
      exact hpos
    · have hle := hmax j (by simp [T, hgj])
      refine lt_of_le_of_ne hle fun heq => hji (hinj ?_)
      rw [ν.map_smul, ν.map_smul] at heq
      have hu : ‖g j / g i₀‖ = ν (b i₀) / ν (b j) := by
        rw [norm_div, div_eq_div_iff (norm_pos_iff.2 hi₀).ne' (hbpos j).ne']
        linear_combination heq
      have h1 : ‖ϖ‖ < ‖g j / g i₀‖ := by
        rw [hu, lt_div_iff₀ (hbpos j)]
        have := (hb j).2
        have h' : ‖ϖ‖ * ν (b j) < ‖ϖ‖ * (‖ϖ‖⁻¹ * c) := mul_lt_mul_of_pos_left this hϖ.1
        rw [← mul_assoc, mul_inv_cancel₀ hϖ.1.ne', one_mul] at h'
        exact h'.trans_le (hb i₀).1
      have h2 : ‖g j / g i₀‖ < ‖ϖ‖⁻¹ := by
        rw [hu, div_lt_iff₀ (hbpos j)]
        exact (hb i₀).2.trans_le (mul_le_mul_of_nonneg_left (hb j).1 (inv_pos.2 hϖ.1).le)
      have h3 := hϖ.norm_eq_one h1 h2
      rw [hu, div_eq_one_iff_eq (hbpos j).ne'] at h3
      exact h3.symm
  have hrest := ν.apply_sum_lt (Finset.univ.erase i₀) (fun j => g j • b j) hpos hlt
  have hsum := ν.apply_add_eq_of_lt hrest
  rw [Finset.add_sum_erase Finset.univ (fun j => g j • b j) (Finset.mem_univ i₀), hg,
    map_zero] at hsum
  exact absurd hsum hpos.ne

theorem card_le_finrank_of_values [FiniteDimensional F V] (hϖ : IsMaxBelowOne ϖ) {ι : Type*}
    [Fintype ι] (b : ι → V) {c : ℝ} (hc : 0 < c)
    (hb : ∀ i, c ≤ ν (b i) ∧ ν (b i) < ‖ϖ‖⁻¹ * c)
    (hinj : Function.Injective fun i => ν (b i)) : Fintype.card ι ≤ Module.finrank F V :=
  (linearIndependent_of_values ν hϖ b hc hb hinj).fintype_card_le_finrank

end Independence

/-! ## The ratio suprema -/

section Ratio

variable {F : Type v} [NormedField F] {V : Type w} [AddCommGroup V] [Module F V]

theorem le_ratioSup (ν μ : VectorNorm F V) (a : V) :
    ENNReal.ofReal (ν a / μ a) ≤ ratioSup ν μ :=
  le_iSup (fun x => ENNReal.ofReal (ν x / μ x)) a

theorem ratioSup_le_ofReal {ν μ : VectorNorm F V} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ a, a ≠ 0 → ν a ≤ C * μ a) : ratioSup ν μ ≤ ENNReal.ofReal C := by
  refine iSup_le fun a => ENNReal.ofReal_le_ofReal ?_
  by_cases ha : a = 0
  · rw [ha, map_zero, zero_div]
    exact hC
  · rw [div_le_iff₀ (μ.pos ha)]
    exact h a ha

theorem ratioSup_le_mul (ν μ ρ : VectorNorm F V) :
    ratioSup ν ρ ≤ ratioSup ν μ * ratioSup μ ρ := by
  refine iSup_le fun a => ?_
  by_cases ha : a = 0
  · rw [ha, map_zero, zero_div, ENNReal.ofReal_zero]
    positivity
  · calc ENNReal.ofReal (ν a / ρ a)
        = ENNReal.ofReal (ν a / μ a) * ENNReal.ofReal (μ a / ρ a) := by
          rw [← ENNReal.ofReal_mul (div_nonneg (ν.nonneg a) (μ.nonneg a)),
            div_mul_div_cancel₀ (μ.pos ha).ne']
      _ ≤ _ := mul_le_mul' (le_ratioSup ν μ a) (le_ratioSup μ ρ a)

/-- The triangle inequality for the Goldman–Iwahori distance, in multiplicative form. -/
theorem distRatio_le_mul (ν μ ρ : VectorNorm F V) :
    distRatio ν ρ ≤ distRatio ν μ * distRatio μ ρ := by
  unfold distRatio
  calc ratioSup ν ρ * ratioSup ρ ν
      ≤ (ratioSup ν μ * ratioSup μ ρ) * (ratioSup ρ μ * ratioSup μ ν) :=
        mul_le_mul' (ratioSup_le_mul ν μ ρ) (ratioSup_le_mul ρ μ ν)
    _ = ratioSup ν μ * ratioSup μ ν * (ratioSup μ ρ * ratioSup ρ μ) := by ring

theorem ratioSup_ne_zero [Nontrivial V] (ν μ : VectorNorm F V) : ratioSup ν μ ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  refine (lt_of_lt_of_le ?_ (le_ratioSup ν μ x)).ne'
  exact ENNReal.ofReal_pos.2 (div_pos (ν.pos hx) (μ.pos hx))

theorem ratioSup_ne_top_of_distRatio_lt [Nontrivial V] {ν μ : VectorNorm F V} {C : ℝ}
    (h : distRatio ν μ < ENNReal.ofReal C) : ratioSup ν μ ≠ ⊤ ∧ ratioSup μ ν ≠ ⊤ := by
  constructor
  · intro htop
    rw [distRatio, htop, ENNReal.top_mul (ratioSup_ne_zero μ ν)] at h
    exact absurd h (not_lt.2 le_top)
  · intro htop
    rw [distRatio, htop, ENNReal.mul_top (ratioSup_ne_zero ν μ)] at h
    exact absurd h (not_lt.2 le_top)

end Ratio

/-! ## Ball norms -/

section Ball

variable {F : Type v} [NontriviallyNormedField F] {ϖ : F} (hϖ : IsMaxBelowOne ϖ)
  {V : Type w} [AddCommGroup V] [Module F V]
include hϖ

/-- The lattice norm `a ↦ up(ν(a) / s)` of the ball `{ν ≤ s}` (for `q = ‖ϖ‖⁻¹`). -/
def ballNorm (ν : VectorNorm F V) {s : ℝ} (hs : 0 < s) : VectorNorm F V where
  toFun a := up ‖ϖ‖⁻¹ (ν a / s)
  pos' a ha := up_pos hϖ.one_lt_inv (div_pos (ν.pos ha) hs)
  smul' t a := by
    by_cases ht : t = 0
    · rw [ht, zero_smul, map_zero, zero_div, up_of_nonpos le_rfl, norm_zero, zero_mul]
    by_cases ha : a = 0
    · rw [ha, smul_zero, map_zero, zero_div, up_of_nonpos le_rfl, mul_zero]
    rw [ν.map_smul]
    obtain ⟨n, hn⟩ := hϖ.exists_norm_eq_zpow ht
    rw [hn, mul_div_assoc, up_zpow_mul hϖ.one_lt_inv n (div_pos (ν.pos ha) hs)]
  add_le_max' a b := by
    by_cases hab : a + b = 0
    · rw [hab, map_zero, zero_div, up_of_nonpos le_rfl]
      exact le_max_of_le_left up_nonneg
    rcases le_max_iff.1 (ν.add_le_max a b) with h | h
    · exact le_max_of_le_left (up_mono hϖ.one_lt_inv (div_pos (ν.pos hab) hs)
        (div_le_div_of_nonneg_right h hs.le))
    · exact le_max_of_le_right (up_mono hϖ.one_lt_inv (div_pos (ν.pos hab) hs)
        (div_le_div_of_nonneg_right h hs.le))

variable (ν : VectorNorm F V)

theorem ballNorm_apply {s : ℝ} (hs : 0 < s) {a : V} (_ha : a ≠ 0) :
    ballNorm hϖ ν hs a = up ‖ϖ‖⁻¹ (ν a / s) := rfl

theorem ballNorm_isLatticeNorm {s : ℝ} (hs : 0 < s) : (ballNorm hϖ ν hs).IsLatticeNorm := by
  intro a
  by_cases ha : a = 0
  · exact ⟨0, by rw [ha, map_zero, norm_zero]⟩
  obtain ⟨n, hn, -, -⟩ := up_spec hϖ.one_lt_inv (div_pos (ν.pos ha) hs)
  refine ⟨ϖ⁻¹ ^ n, ?_⟩
  rw [ballNorm_apply hϖ ν hs ha, hn, norm_zpow, norm_inv]

theorem div_le_ballNorm {s : ℝ} (hs : 0 < s) (a : V) : ν a / s ≤ ballNorm hϖ ν hs a := by
  by_cases ha : a = 0
  · rw [ha, map_zero, map_zero, zero_div]
  rw [ballNorm_apply hϖ ν hs ha]
  exact le_up hϖ.one_lt_inv (div_pos (ν.pos ha) hs)

theorem ballNorm_le {s : ℝ} (hs : 0 < s) (a : V) :
    ballNorm hϖ ν hs a ≤ ‖ϖ‖⁻¹ * (ν a / s) := by
  by_cases ha : a = 0
  · rw [ha, map_zero, map_zero, zero_div, mul_zero]
  rw [ballNorm_apply hϖ ν hs ha]
  exact (up_lt hϖ.one_lt_inv (div_pos (ν.pos ha) hs)).le

/-- A norm is at distance at most `q` from each of its ball norms. -/
theorem distRatio_ballNorm_le {s : ℝ} (hs : 0 < s) :
    distRatio ν (ballNorm hϖ ν hs) ≤ ENNReal.ofReal ‖ϖ‖⁻¹ := by
  have hq : 0 < ‖ϖ‖⁻¹ := inv_pos.2 hϖ.1
  have h1 : ratioSup ν (ballNorm hϖ ν hs) ≤ ENNReal.ofReal s :=
    ratioSup_le_ofReal hs.le fun a _ => by
      have := div_le_ballNorm hϖ ν hs a
      rwa [div_le_iff₀' hs] at this
  have h2 : ratioSup (ballNorm hϖ ν hs) ν ≤ ENNReal.ofReal (‖ϖ‖⁻¹ / s) :=
    ratioSup_le_ofReal (div_pos hq hs).le fun a _ =>
      (ballNorm_le hϖ ν hs a).trans_eq (by ring)
  calc distRatio ν (ballNorm hϖ ν hs) ≤ ENNReal.ofReal s * ENNReal.ofReal (‖ϖ‖⁻¹ / s) :=
        mul_le_mul' h1 h2
    _ = ENNReal.ofReal ‖ϖ‖⁻¹ := by
        rw [← ENNReal.ofReal_mul hs.le, mul_div_cancel₀ _ hs.ne']

theorem ballNorm_anti {s s' : ℝ} (hs : 0 < s) (hss' : s ≤ s') (a : V) :
    ballNorm hϖ ν (hs.trans_le hss') a ≤ ballNorm hϖ ν hs a := by
  by_cases ha : a = 0
  · rw [ha, map_zero, map_zero]
  rw [ballNorm_apply hϖ ν _ ha, ballNorm_apply hϖ ν _ ha]
  exact up_mono hϖ.one_lt_inv (div_pos (ν.pos ha) (hs.trans_le hss'))
    (div_le_div_of_nonneg_left (ν.nonneg a) hs hss')

theorem ballNorm_zpow_mul {s : ℝ} (hs : 0 < s) (k : ℤ) (a : V) :
    ballNorm hϖ ν (mul_pos (zpow_pos (inv_pos.2 hϖ.1) k) hs) a =
      ‖ϖ‖⁻¹ ^ (-k) * ballNorm hϖ ν hs a := by
  by_cases ha : a = 0
  · rw [ha, map_zero, map_zero, mul_zero]
  have hq : 0 < ‖ϖ‖⁻¹ := inv_pos.2 hϖ.1
  rw [ballNorm_apply hϖ ν _ ha, ballNorm_apply hϖ ν _ ha, ← up_zpow_mul hϖ.one_lt_inv (-k)
    (div_pos (ν.pos ha) hs), zpow_neg, div_mul_eq_div_div, inv_mul_eq_div]
  congr 1
  rw [div_div, div_div, mul_comm]

/-- If `s ≤ q s'`, then `β_{s'} ≤ q β_s`. -/
theorem ballNorm_le_mul {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s') (h : s ≤ ‖ϖ‖⁻¹ * s') (a : V) :
    ballNorm hϖ ν hs' a ≤ ‖ϖ‖⁻¹ * ballNorm hϖ ν hs a := by
  by_cases ha : a = 0
  · rw [ha, map_zero, map_zero, mul_zero]
  rw [ballNorm_apply hϖ ν hs' ha, ballNorm_apply hϖ ν hs ha]
  have := up_zpow_mul hϖ.one_lt_inv 1 (div_pos (ν.pos ha) hs)
  rw [zpow_one] at this
  rw [← this]
  apply up_mono hϖ.one_lt_inv (div_pos (ν.pos ha) hs')
  rw [div_le_iff₀ hs']
  calc ν a = ν a / s * s := (div_mul_cancel₀ _ hs.ne').symm
    _ ≤ ν a / s * (‖ϖ‖⁻¹ * s') := mul_le_mul_of_nonneg_left h (div_pos (ν.pos ha) hs).le
    _ = ‖ϖ‖⁻¹ * (ν a / s) * s' := by ring

/-- A lattice norm at distance less than `q` from `ν` is a ball norm of `ν`. -/
theorem eq_ballNorm [Nontrivial V] {μ : VectorNorm F V} (hμ : μ.IsLatticeNorm)
    (h : distRatio ν μ < ENNReal.ofReal ‖ϖ‖⁻¹) : ∃ (s : ℝ) (hs : 0 < s), μ = ballNorm hϖ ν hs := by
  obtain ⟨hR, hr⟩ := ratioSup_ne_top_of_distRatio_lt h
  have hR0 := ratioSup_ne_zero ν μ
  have hr0 := ratioSup_ne_zero μ ν
  set R := (ratioSup ν μ).toReal with hR_def
  set r := (ratioSup μ ν).toReal with hr_def
  have hRpos : 0 < R := ENNReal.toReal_pos hR0 hR
  have hrpos : 0 < r := ENNReal.toReal_pos hr0 hr
  have hRr : R * r < ‖ϖ‖⁻¹ := by
    rw [hR_def, hr_def, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_lt_of_lt_ofReal h
  refine ⟨R, hRpos, VectorNorm.ext fun a => ?_⟩
  by_cases ha : a = 0
  · rw [ha, map_zero, map_zero]
  rw [ballNorm_apply hϖ ν hRpos ha]
  have h1 : ν a / μ a ≤ R :=
    (ENNReal.ofReal_le_iff_le_toReal hR).1 (le_ratioSup ν μ a)
  have h2 : μ a / ν a ≤ r :=
    (ENNReal.ofReal_le_iff_le_toReal hr).1 (le_ratioSup μ ν a)
  have hνa := ν.pos ha
  have hμa := μ.pos ha
  obtain ⟨t, ht⟩ := hμ a
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [norm_zero] at ht
    exact hμa.ne' ht
  obtain ⟨n, hn⟩ := hϖ.exists_norm_eq_zpow ht0
  rw [ht, hn]
  symm
  apply up_eq_of hϖ.one_lt_inv (div_pos hνa hRpos)
  · rw [← hn, ← ht, div_le_iff₀ hRpos]
    rw [div_le_iff₀ hμa] at h1
    linarith
  · rw [← hn, ← ht]
    rw [div_le_iff₀ hνa] at h2
    have h3 : μ a * R ≤ r * ν a * R := mul_le_mul_of_nonneg_right h2 hRpos.le
    have h4 : r * ν a * R < ‖ϖ‖⁻¹ * ν a := by
      have := mul_lt_mul_of_pos_right hRr hνa
      linarith
    rw [mul_div_assoc', lt_div_iff₀ hRpos]
    linarith

theorem ballNorm_congr {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s') (h : s = s') :
    ballNorm hϖ ν hs = ballNorm hϖ ν hs' := by
  subst h
  rfl

/-- A ball norm `β_s` is homothetic to `β_{q^k s}`. -/
theorem homothetic_ballNorm_zpow_mul {s : ℝ} (hs : 0 < s) (k : ℤ) :
    Homothetic (ballNorm hϖ ν hs) (ballNorm hϖ ν (mul_pos (zpow_pos (inv_pos.2 hϖ.1) k) hs)) :=
  ⟨‖ϖ‖⁻¹ ^ (-k), zpow_pos (inv_pos.2 hϖ.1) _, fun a => ballNorm_zpow_mul hϖ ν hs k a⟩

/-- Every lattice norm at distance less than `q` from `ν` is homothetic to a ball norm `β_s`
with `1 ≤ s < q`. -/
theorem exists_ballNorm_class [Nontrivial V] {μ : VectorNorm F V} (hμ : μ.IsLatticeNorm)
    (h : distRatio ν μ < ENNReal.ofReal ‖ϖ‖⁻¹) :
    ∃ (s : ℝ) (hs : 1 ≤ s), s < ‖ϖ‖⁻¹ ∧
      (⟦μ⟧ : NormClass F V) = ⟦ballNorm hϖ ν (zero_lt_one.trans_le hs)⟧ := by
  obtain ⟨R, hR, rfl⟩ := eq_ballNorm hϖ ν hμ h
  have hQ : 0 < ‖ϖ‖⁻¹ := inv_pos.2 hϖ.1
  obtain ⟨n, hn₁, hn₂⟩ := exists_mem_Ico_zpow hR hϖ.one_lt_inv
  have h1 : 1 ≤ ‖ϖ‖⁻¹ ^ (-n) * R := by
    rw [zpow_neg, ← div_eq_inv_mul, le_div_iff₀ (zpow_pos hQ n), one_mul]
    exact hn₁
  have h2 : ‖ϖ‖⁻¹ ^ (-n) * R < ‖ϖ‖⁻¹ := by
    rw [zpow_neg, ← div_eq_inv_mul, div_lt_iff₀ (zpow_pos hQ n), ← zpow_one_add₀ hQ.ne',
      add_comm]
    exact hn₂
  refine ⟨_, h1, h2, Quotient.sound ?_⟩
  exact homothetic_ballNorm_zpow_mul hϖ ν hR (-n)

/-- If no value of `ν` lies in `(s, s']`, the ball norms for `s` and `s'` agree. -/
theorem ballNorm_eq_of_no_value {s s' : ℝ} (hs : 0 < s) (hss' : s ≤ s')
    (h : ∀ b : V, ¬ (s < ν b ∧ ν b ≤ s')) :
    ballNorm hϖ ν (hs.trans_le hss') = ballNorm hϖ ν hs := by
  have hQ : 0 < ‖ϖ‖⁻¹ := inv_pos.2 hϖ.1
  have hs' := hs.trans_le hss'
  refine VectorNorm.ext fun a => ?_
  by_cases ha : a = 0
  · rw [ha, map_zero, map_zero]
  have hνa := ν.pos ha
  rw [ballNorm_apply hϖ ν hs' ha, ballNorm_apply hϖ ν hs ha]
  obtain ⟨n, hn, hn₁, hn₂⟩ := up_spec hϖ.one_lt_inv (div_pos hνa hs')
  rw [hn]
  symm
  apply up_eq_of hϖ.one_lt_inv (div_pos hνa hs)
  · by_contra hlt
    push Not at hlt
    apply h ((ϖ⁻¹) ^ (-n) • a)
    rw [ν.map_smul, norm_zpow, norm_inv]
    constructor
    · rw [lt_div_iff₀ hs] at hlt
      rw [zpow_neg, ← div_eq_inv_mul, lt_div_iff₀ (zpow_pos hQ n), mul_comm]
      exact hlt
    · rw [div_le_iff₀ hs'] at hn₁
      rw [zpow_neg, ← div_eq_inv_mul, div_le_iff₀ (zpow_pos hQ n), mul_comm]
      exact hn₁
  · refine hn₂.trans_le (mul_le_mul_of_nonneg_left ?_ hQ.le)
    exact div_le_div_of_nonneg_left hνa.le hs hss'

/-- The set of values of `ν` in `[1, q)` is finite. -/
theorem finite_values [FiniteDimensional F V] :
    {x : ℝ | ∃ b : V, ν b = x ∧ 1 ≤ x ∧ x < ‖ϖ‖⁻¹}.Finite := by
  by_contra hinf
  obtain ⟨t, hts, htcard⟩ :=
    Set.Infinite.exists_subset_card_eq hinf (Module.finrank F V + 1)
  have hmem : ∀ x : t, ∃ b : V, ν b = x ∧ 1 ≤ (x : ℝ) ∧ (x : ℝ) < ‖ϖ‖⁻¹ := fun x => hts x.2
  choose b hb using hmem
  have hcard := card_le_finrank_of_values ν hϖ b one_pos
    (fun x => by rw [(hb x).1, mul_one]; exact ⟨(hb x).2.1, (hb x).2.2⟩)
    (fun x y hxy => by
      simp only [(hb x).1, (hb y).1] at hxy
      exact Subtype.ext hxy)
  rw [Fintype.card_coe, htcard] at hcard
  omega

/-- A gap in the values of `ν`: if `λ ^ N ≤ q` with `N = dim V` and `λ > 1`, some nonzero value
`ν(a₀)` has no value in `(ν(a₀), λ ν(a₀))`. -/
theorem exists_value_gap [FiniteDimensional F V] [Nontrivial V] {lam : ℝ} (hlam : 1 < lam)
    (hlamN : lam ^ Module.finrank F V ≤ ‖ϖ‖⁻¹) :
    ∃ a₀ : V, a₀ ≠ 0 ∧ ∀ b : V, ¬ (ν a₀ < ν b ∧ ν b < lam * ν a₀) := by
  by_contra H
  push Not at H
  have H' : ∀ a : {a : V // a ≠ 0}, ∃ b : {a : V // a ≠ 0},
      ν a < ν b ∧ ν b < lam * ν a := by
    intro a
    obtain ⟨b, hb⟩ := H a.1 a.2
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [map_zero] at hb
      exact absurd hb.1 (not_lt.2 (ν.nonneg _))
    exact ⟨⟨b, hb0⟩, hb⟩
  choose f hf using H'
  obtain ⟨a₀, ha₀⟩ := exists_ne (0 : V)
  set seq : ℕ → {a : V // a ≠ 0} := fun n => f^[n] ⟨a₀, ha₀⟩ with hseq
  have hsucc : ∀ n, seq (n + 1) = f (seq n) := fun n =>
    Function.iterate_succ_apply' f n _
  set v : ℕ → ℝ := fun n => ν (seq n) with hv
  have hv0 : 0 < v 0 := ν.pos (seq 0).2
  have hstep : ∀ n, v n < v (n + 1) ∧ v (n + 1) < lam * v n := fun n => by
    simp only [hv, hsucc]
    exact hf (seq n)
  have hmono : StrictMono v := strictMono_nat_of_lt_succ fun n => (hstep n).1
  have hupper : ∀ n, v (n + 1) < lam ^ (n + 1) * v 0 := by
    intro n
    induction n with
    | zero => simpa using (hstep 0).2
    | succ n ih =>
      calc v (n + 1 + 1) < lam * v (n + 1) := (hstep (n + 1)).2
        _ < lam * (lam ^ (n + 1) * v 0) := mul_lt_mul_of_pos_left ih (by linarith)
        _ = lam ^ (n + 1 + 1) * v 0 := by ring
  set N := Module.finrank F V
  have hcard := card_le_finrank_of_values ν hϖ (fun i : Fin (N + 1) => ((seq i).1 : V)) hv0
    (fun i => by
      refine ⟨hmono.monotone (Nat.zero_le _), ?_⟩
      change v i < _
      rcases Nat.eq_zero_or_eq_succ_pred (i : ℕ) with h0 | hpos
      · rw [h0]
        have := hϖ.one_lt_inv
        nlinarith
      · rw [hpos]
        refine (hupper _).trans_le (mul_le_mul_of_nonneg_right ?_ hv0.le)
        refine le_trans (pow_le_pow_right₀ hlam.le ?_) hlamN
        have := i.2
        omega)
    (fun i j hij => Fin.ext (hmono.injective hij))
  rw [Fintype.card_fin] at hcard
  omega

/-- At a gap of the values, the ball norm is at distance at most `q / λ`. -/
theorem distRatio_ballNorm_le_of_gap {a₀ : V} (ha₀ : a₀ ≠ 0) {lam : ℝ} (hlam : 0 < lam)
    (hgap : ∀ b : V, ¬ (ν a₀ < ν b ∧ ν b < lam * ν a₀)) :
    distRatio ν (ballNorm hϖ ν (ν.pos ha₀)) ≤ ENNReal.ofReal (‖ϖ‖⁻¹ / lam) := by
  have hQ : 0 < ‖ϖ‖⁻¹ := inv_pos.2 hϖ.1
  set v₀ := ν a₀ with hv₀
  have hv₀pos : 0 < v₀ := ν.pos ha₀
  have h1 : ratioSup ν (ballNorm hϖ ν hv₀pos) ≤ ENNReal.ofReal v₀ :=
    ratioSup_le_ofReal hv₀pos.le fun a _ => by
      have := div_le_ballNorm hϖ ν hv₀pos a
      rwa [div_le_iff₀' hv₀pos] at this
  have h2 : ratioSup (ballNorm hϖ ν hv₀pos) ν ≤ ENNReal.ofReal (‖ϖ‖⁻¹ / (lam * v₀)) := by
    refine ratioSup_le_ofReal (div_pos hQ (mul_pos hlam hv₀pos)).le fun a ha => ?_
    have hνa := ν.pos ha
    set w := ν a / v₀ with hw
    have hwpos : 0 < w := div_pos hνa hv₀pos
    rw [ballNorm_apply hϖ ν hv₀pos ha]
    obtain ⟨n, hn, hn₁, hn₂⟩ := up_spec hϖ.one_lt_inv hwpos
    obtain ⟨k, rfl⟩ : ∃ k : ℤ, n = k + 1 := ⟨n - 1, by ring⟩
    rw [zpow_add_one₀ hQ.ne'] at hn hn₂
    have hk : ‖ϖ‖⁻¹ ^ k < w := by
      rw [mul_comm] at hn₂
      exact lt_of_mul_lt_mul_left hn₂ hQ.le
    have hlamk : lam * ‖ϖ‖⁻¹ ^ k ≤ w := by
      by_contra hlt
      push Not at hlt
      apply hgap ((ϖ⁻¹) ^ (-k) • a)
      rw [ν.map_smul, norm_zpow, norm_inv, zpow_neg, ← div_eq_inv_mul]
      have hνa' : ν a = w * v₀ := by rw [hw, div_mul_cancel₀ _ hv₀pos.ne']
      rw [hνa', mul_div_right_comm]
      have hQk := zpow_pos hQ k
      constructor
      · rw [lt_mul_iff_one_lt_left hv₀pos, one_lt_div hQk]
        exact hk
      · rw [mul_lt_mul_iff_left₀ hv₀pos, div_lt_iff₀ hQk]
        exact hlt
    rw [hn]
    have hνa' : ν a = w * v₀ := by rw [hw, div_mul_cancel₀ _ hv₀pos.ne']
    rw [hνa', div_mul_eq_mul_div, le_div_iff₀ (mul_pos hlam hv₀pos)]
    have := mul_le_mul_of_nonneg_left hlamk hQ.le
    nlinarith
  calc distRatio ν (ballNorm hϖ ν (ν.pos ha₀))
      ≤ ENNReal.ofReal v₀ * ENNReal.ofReal (‖ϖ‖⁻¹ / (lam * v₀)) := mul_le_mul' h1 h2
    _ = ENNReal.ofReal (‖ϖ‖⁻¹ / lam) := by
        rw [← ENNReal.ofReal_mul hv₀pos.le]
        congr 1
        field_simp

end Ball

end VectorNorm

/-! ## Nearest vertices -/

namespace NormClass

section Triangle

variable {F : Type v} [NormedField F] {V : Type w} [AddCommGroup V] [Module F V]

/-- The triangle inequality for the Goldman–Iwahori distance on norm classes. -/
theorem distRatio_le_mul (x y z : NormClass F V) :
    distRatio x z ≤ distRatio x y * distRatio y z :=
  Quotient.inductionOn₃ x y z VectorNorm.distRatio_le_mul

end Triangle

variable {F : Type v} [NontriviallyNormedField F] {ϖ : F} (hϖ : VectorNorm.IsMaxBelowOne ϖ)
  {V : Type w} [AddCommGroup V] [Module F V]

/-- The gap constant `λ = q ^ (1 / N)`, `q = ‖ϖ‖⁻¹`, `N = dim V`. -/
def gapConst (ϖ : F) (N : ℕ) : ℝ := Real.exp (Real.log ‖ϖ‖⁻¹ / N)

include hϖ

theorem one_lt_gapConst {N : ℕ} (hN : 0 < N) : 1 < gapConst ϖ N :=
  Real.one_lt_exp_iff.2 (div_pos (Real.log_pos hϖ.one_lt_inv) (by exact_mod_cast hN))

theorem gapConst_pow {N : ℕ} (hN : 0 < N) : gapConst ϖ N ^ N = ‖ϖ‖⁻¹ := by
  rw [gapConst, ← Real.exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hN.ne'),
    Real.exp_log (inv_pos.2 hϖ.1)]

variable [FiniteDimensional F V] [Nontrivial V]

/-- Every point of the building is at distance at most `q / λ` from a vertex. -/
theorem exists_vertex_distRatio_le (x : NormClass F V) :
    ∃ e, IsVertex e ∧
      distRatio x e ≤ ENNReal.ofReal (‖ϖ‖⁻¹ / gapConst ϖ (Module.finrank F V)) := by
  obtain ⟨ν, rfl⟩ := Quotient.exists_rep x
  have hN := Module.finrank_pos (R := F) (M := V)
  obtain ⟨a₀, ha₀, hgap⟩ := VectorNorm.exists_value_gap hϖ ν (one_lt_gapConst hϖ hN)
    (gapConst_pow hϖ hN).le
  refine ⟨⟦VectorNorm.ballNorm hϖ ν (ν.pos ha₀)⟧,
    ⟨_, rfl, VectorNorm.ballNorm_isLatticeNorm hϖ ν _⟩, ?_⟩
  exact VectorNorm.distRatio_ballNorm_le_of_gap hϖ ν ha₀
    (zero_lt_one.trans (one_lt_gapConst hϖ hN)) hgap

/-- Only finitely many vertices are at distance less than `q` from a given point. -/
theorem finite_near_vertices (x : NormClass F V) :
    {e | IsVertex e ∧ distRatio x e < ENNReal.ofReal ‖ϖ‖⁻¹}.Finite := by
  obtain ⟨ν, rfl⟩ := Quotient.exists_rep x
  set P := insert (1 : ℝ) {x : ℝ | ∃ b : V, ν b = x ∧ 1 ≤ x ∧ x < ‖ϖ‖⁻¹} with hP
  have hPfin : P.Finite := (VectorNorm.finite_values hϖ ν).insert 1
  have hPpos : ∀ p ∈ P, 1 ≤ p := by
    intro p hp
    rcases hp with rfl | ⟨_, _, h, _⟩
    · exact le_rfl
    · exact h
  have := hPfin.to_subtype
  refine (Set.finite_range fun p : P =>
    (⟦VectorNorm.ballNorm hϖ ν (zero_lt_one.trans_le (hPpos p.1 p.2))⟧ : NormClass F V)).subset ?_
  rintro e ⟨⟨μ, rfl, hμ⟩, he⟩
  obtain ⟨s, hs1, hsQ, hse⟩ := VectorNorm.exists_ballNorm_class hϖ ν hμ he
  set T := insert (1 : ℝ) {p ∈ P | p ≤ s} with hT
  have hTfin : T.Finite := (hPfin.subset (fun p hp => hp.1)).insert 1
  obtain ⟨m, hmT, hmax⟩ := Set.exists_max_image T id hTfin ⟨1, Set.mem_insert _ _⟩
  have hmP : m ∈ P := by
    rcases hmT with rfl | hm
    · exact Set.mem_insert _ _
    · exact hm.1
  have hms : m ≤ s := by
    rcases hmT with rfl | hm
    · exact hs1
    · exact hm.2
  have hm1 : 1 ≤ m := hPpos m hmP
  refine ⟨⟨m, hmP⟩, ?_⟩
  rw [hse]
  change (⟦VectorNorm.ballNorm hϖ ν _⟧ : NormClass F V) = ⟦VectorNorm.ballNorm hϖ ν _⟧
  congr 1
  rw [← VectorNorm.ballNorm_eq_of_no_value hϖ ν (zero_lt_one.trans_le hm1) hms]
  · rintro b ⟨hb₁, hb₂⟩
    have hbP : ν b ∈ P :=
      Set.mem_insert_of_mem _ ⟨b, rfl, hm1.trans hb₁.le, hb₂.trans_lt hsQ⟩
    exact absurd (hmax (ν b) (Set.mem_insert_of_mem _ ⟨hbP, hb₂⟩)) (not_le.2 hb₁)

/-- Every point of the building lies in the star of a vertex. -/
theorem exists_mem_vertexStar (x : NormClass F V) : ∃ e, IsVertex e ∧ x ∈ vertexStar e := by
  have hN := Module.finrank_pos (R := F) (M := V)
  have hQ : 0 < ‖ϖ‖⁻¹ := inv_pos.2 hϖ.1
  obtain ⟨e₀, he₀, hd₀⟩ := exists_vertex_distRatio_le hϖ x
  have hlt : ENNReal.ofReal (‖ϖ‖⁻¹ / gapConst ϖ (Module.finrank F V)) <
      ENNReal.ofReal ‖ϖ‖⁻¹ := by
    rw [ENNReal.ofReal_lt_ofReal_iff hQ]
    exact div_lt_self hQ (one_lt_gapConst hϖ hN)
  obtain ⟨e, ⟨he, hex⟩, hmin⟩ := Set.exists_min_image _ (distRatio x)
    (finite_near_vertices hϖ x) ⟨e₀, he₀, hd₀.trans_lt hlt⟩
  refine ⟨e, he, fun e' he' => ?_⟩
  by_cases h' : distRatio x e' < ENNReal.ofReal ‖ϖ‖⁻¹
  · exact hmin e' ⟨he', h'⟩
  · exact hex.le.trans (not_lt.1 h')

/-- A point of the star of `e` is at distance at most `q / λ` from `e`. -/
theorem distRatio_le_of_mem_vertexStar {x e : NormClass F V} (hx : x ∈ vertexStar e) :
    distRatio x e ≤ ENNReal.ofReal (‖ϖ‖⁻¹ / gapConst ϖ (Module.finrank F V)) := by
  obtain ⟨e₀, he₀, hd₀⟩ := exists_vertex_distRatio_le hϖ x
  exact (hx e₀ he₀).trans hd₀

omit [FiniteDimensional F V] in
/-- A nonempty finite set of vertices at distance less than `q` from one point is a facet: its
elements are classes of ball norms `β_s` of the point with `1 ≤ s < q`, and these form a chain
of lattices when ordered by decreasing `s`. -/
theorem isFacet_of_distRatio_lt (x : NormClass F V) (S : Finset (NormClass F V))
    (hS : S.Nonempty) (h : ∀ e ∈ S, IsVertex e ∧ distRatio x e < ENNReal.ofReal ‖ϖ‖⁻¹) :
    IsFacet (S : Set (NormClass F V)) := by
  classical
  obtain ⟨ν, rfl⟩ := Quotient.exists_rep x
  have key : ∀ e ∈ S, ∃ (s : ℝ) (hs : 1 ≤ s), s < ‖ϖ‖⁻¹ ∧
      e = ⟦VectorNorm.ballNorm hϖ ν (zero_lt_one.trans_le hs)⟧ := by
    intro e he
    obtain ⟨⟨μ, rfl, hμ⟩, hd⟩ := h e he
    exact VectorNorm.exists_ballNorm_class hϖ ν hμ hd
  choose! sf hs1 hsQ hse using key
  set T := S.image sf with hT
  have hTpos : ∀ t ∈ T, 1 ≤ t := by
    intro t ht
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 ht
    exact hs1 e he
  have hTlt : ∀ t ∈ T, t < ‖ϖ‖⁻¹ := by
    intro t ht
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 ht
    exact hsQ e he
  have hinj : Set.InjOn sf S := by
    intro e he e' he' hee'
    rw [hse e he, hse e' he']
    exact congrArg _ (VectorNorm.ballNorm_congr hϖ ν _ _ hee')
  have hTcard : T.card = S.card := Finset.card_image_of_injOn hinj
  obtain ⟨k, hk⟩ : ∃ k, T.card = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by rw [hTcard]; exact hS.card_pos.ne')
  set g := T.orderEmbOfFin hk with hg
  have hgT : ∀ i, g i ∈ T := fun i => Finset.orderEmbOfFin_mem T hk i
  have hgpos : ∀ i, 0 < g i := fun i => zero_lt_one.trans_le (hTpos _ (hgT i))
  refine ⟨k, fun i => VectorNorm.ballNorm hϖ ν (hgpos (Fin.rev i)), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i
    exact VectorNorm.ballNorm_isLatticeNorm hϖ ν _
  · intro i j hij a
    have hle : g (Fin.rev j) ≤ g (Fin.rev i) := g.monotone (Fin.rev_le_rev.2 hij)
    exact VectorNorm.ballNorm_anti hϖ ν (hgpos _) hle a
  · intro t ht a
    have hcond : g (Fin.rev 0) ≤ ‖ϖ‖⁻¹ * g (Fin.rev (Fin.last k)) := by
      rw [Fin.rev_zero, Fin.rev_last]
      calc g (Fin.last k) ≤ ‖ϖ‖⁻¹ := (hTlt _ (hgT _)).le
        _ = ‖ϖ‖⁻¹ * 1 := (mul_one _).symm
        _ ≤ ‖ϖ‖⁻¹ * g 0 :=
          mul_le_mul_of_nonneg_left (hTpos _ (hgT 0)) (inv_pos.2 hϖ.1).le
    have hle := VectorNorm.ballNorm_le_mul hϖ ν (hgpos (Fin.rev 0))
      (hgpos (Fin.rev (Fin.last k))) hcond a
    have ht' := hϖ.2.2 t ht
    calc ‖t‖ * VectorNorm.ballNorm hϖ ν (hgpos (Fin.rev (Fin.last k))) a
        ≤ ‖ϖ‖ * (‖ϖ‖⁻¹ * VectorNorm.ballNorm hϖ ν (hgpos (Fin.rev 0)) a) :=
          mul_le_mul ht' hle ((VectorNorm.ballNorm hϖ ν _).nonneg a) hϖ.1.le
      _ = VectorNorm.ballNorm hϖ ν (hgpos (Fin.rev 0)) a := by
          rw [← mul_assoc, mul_inv_cancel₀ hϖ.1.ne', one_mul]
  · ext e
    simp only [Finset.mem_coe, Set.mem_range]
    constructor
    · intro he
      have hmem : sf e ∈ Set.range g := by
        rw [hg, Finset.range_orderEmbOfFin]
        exact Finset.mem_image_of_mem sf he
      obtain ⟨j, hj⟩ := hmem
      refine ⟨Fin.rev j, ?_⟩
      rw [hse e he]
      exact congrArg _ (VectorNorm.ballNorm_congr hϖ ν _ _ (by rw [Fin.rev_rev, hj]))
    · rintro ⟨i, rfl⟩
      obtain ⟨e, he, hei⟩ := Finset.mem_image.1 (hgT (Fin.rev i))
      have heq : (⟦VectorNorm.ballNorm hϖ ν (hgpos (Fin.rev i))⟧ : NormClass F V) = e := by
        rw [hse e he]
        exact congrArg _ (VectorNorm.ballNorm_congr hϖ ν _ _ hei.symm)
      rw [heq]
      exact he

end NormClass

end Langlands.Analytic
