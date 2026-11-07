import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# A dyadic Mellin functional equation on cones

A `DyadicCone E` is a measurable cone `C` in a finite-dimensional real space `E` with a positive
function `N` on `C` satisfying `N (t • x) = t ^ dim E * N x` for `t > 0` (the model is the norm
on a fundamental cone of the mixed space of a number field). The cone is cut into the dyadic
shells `piece k = {x ∈ C | 2^(n(k-1)) < N x ≤ 2^(nk)}`, `n = dim E`, which are images of
`piece 0` under `x ↦ 2^k • x`.

`ThetaData` packages a weight `χ` with `χ (2 • x) = l * χ x` and two functions `f`, `g`
related on `C` by a theta relation `f x + A = N(x)⁻¹ (g x + B)`, with `f χ` rapidly
decreasing on `N > 1` and `g χ` rapidly decreasing on `N ≤ 1`. For such data we define a
function `M` on all of `ℂ` (a holomorphic part plus two terms with explicit poles, obtained by
summing geometric series over the shells) and prove that it is meromorphic, equals the
Mellin integral `∫_C f χ N^(s-1)` for `Re s` large, and that `M (1 - s)` equals the dual
integral `∫_C g χ N^(-s-1)` for `Re s` large.

## Main results

* `hasDerivAt_setIntegral_mul_cpow`, `differentiable_setIntegral_mul_cpow`: holomorphy of
  `z ↦ ∫_S h N^z` when `‖h‖ N^σ` is integrable on `S` for every real `σ`.
* `DyadicCone.integral_lower_of_scaling`, `DyadicCone.integral_upper_of_scaling`: geometric
  summation over the shells of functions with `Φ (2^k • y) = c^k Φ y`.
* `DyadicCone.ThetaData.meromorphicOn_M`, `DyadicCone.ThetaData.M_eq_integral`,
  `DyadicCone.ThetaData.M_one_sub_eq_integral`, `DyadicCone.ThetaData.exists_re_gt`.
-/

open MeasureTheory Set Filter Module
open scoped Topology

noncomputable section

namespace Langlands.Global.Hecke

/-! ### Holomorphy of integrals of complex powers -/

lemma abs_log_le_add_inv {y : ℝ} (hy : 0 < y) : |Real.log y| ≤ y + y⁻¹ := by
  have hy' : 0 < y⁻¹ := inv_pos.mpr hy
  rcases le_or_gt 1 y with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    linarith [Real.log_le_sub_one_of_pos hy]
  · rw [abs_of_neg (Real.log_neg hy h)]
    have := Real.log_le_sub_one_of_pos hy'
    rw [Real.log_inv] at this
    linarith

lemma rpow_le_add_rpow {y a b : ℝ} (hy : 0 < y) (h : |a - b| ≤ 1) :
    y ^ a ≤ y ^ (b + 1) + y ^ (b - 1) := by
  have h' := abs_le.mp h
  rcases le_or_gt 1 y with h1 | h1
  · have : y ^ a ≤ y ^ (b + 1) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    linarith [Real.rpow_pos_of_pos hy (b - 1)]
  · have : y ^ a ≤ y ^ (b - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hy h1.le (by linarith)
    linarith [Real.rpow_pos_of_pos hy (b + 1)]

section Holomorphy

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Integrals `∫_S h(x) N(x)^z` are holomorphic in `z` as soon as `‖h‖ N^σ` is integrable on `S`
for every real `σ`. -/
theorem hasDerivAt_setIntegral_mul_cpow {S : Set X} (hS : MeasurableSet S) {N : X → ℝ}
    (hN : Measurable N) (hpos : ∀ x ∈ S, 0 < N x) {h : X → ℂ}
    (hmeas : AEStronglyMeasurable h (μ.restrict S))
    (hint : ∀ σ : ℝ, IntegrableOn (fun x => ‖h x‖ * N x ^ σ) S μ) (s : ℂ) :
    HasDerivAt (fun z : ℂ => ∫ x in S, h x * (N x : ℂ) ^ z ∂μ)
      (∫ x in S, h x * (N x : ℂ) ^ s * (Real.log (N x) : ℂ) ∂μ) s := by
  have hcpow : ∀ z : ℂ, AEStronglyMeasurable (fun x => (N x : ℂ) ^ z) (μ.restrict S) :=
    fun z => ((Complex.measurable_ofReal.comp hN).pow_const z).aestronglyMeasurable
  have hnorm : ∀ z : ℂ, ∀ x ∈ S, ‖(N x : ℂ) ^ z‖ = N x ^ z.re := fun z x hx =>
    Complex.norm_cpow_eq_rpow_re_of_pos (hpos x hx) z
  let bound : X → ℝ := fun x =>
    ‖h x‖ * (N x ^ (s.re + 2) + 2 * N x ^ s.re + N x ^ (s.re - 2))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict S)
    (F := fun z x => h x * (N x : ℂ) ^ z)
    (F' := fun z x => h x * (N x : ℂ) ^ z * (Real.log (N x) : ℂ)) (bound := bound)
    (Metric.ball_mem_nhds s one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Eventually.of_forall fun z => hmeas.mul (hcpow z)
  · refine Integrable.mono' (hint s.re) (hmeas.mul (hcpow s)) ?_
    refine (ae_restrict_mem hS).mono fun x hx => ?_
    rw [norm_mul, hnorm s x hx]
  · exact (hmeas.mul (hcpow s)).mul
      (Complex.measurable_ofReal.comp (Real.measurable_log.comp hN)).aestronglyMeasurable
  · refine (ae_restrict_mem hS).mono fun x hx z hz => ?_
    have hx0 := hpos x hx
    have hNx := hx0.ne'
    rw [norm_mul, norm_mul, hnorm z x hx, Complex.norm_real, Real.norm_eq_abs]
    have hz' : |z.re - s.re| ≤ 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have := Complex.abs_re_le_norm (z - s)
      rw [Complex.sub_re] at this
      linarith
    have h1 := rpow_le_add_rpow hx0 hz'
    have h2 := abs_log_le_add_inv hx0
    have e1 : N x ^ (s.re + 1) = N x ^ s.re * N x := Real.rpow_add_one hNx _
    have e2 : N x ^ (s.re - 1) = N x ^ s.re / N x := Real.rpow_sub_one hNx _
    have e3 : N x ^ (s.re + 2) = N x ^ s.re * N x * N x := by
      rw [show s.re + 2 = s.re + 1 + 1 by ring, Real.rpow_add_one hNx, e1]
    have e4 : N x ^ (s.re - 2) = N x ^ s.re / N x / N x := by
      rw [show s.re - 2 = s.re - 1 - 1 by ring, Real.rpow_sub_one hNx, e2]
    have key : N x ^ z.re * |Real.log (N x)| ≤
        N x ^ (s.re + 2) + 2 * N x ^ s.re + N x ^ (s.re - 2) := by
      calc N x ^ z.re * |Real.log (N x)| ≤
            (N x ^ (s.re + 1) + N x ^ (s.re - 1)) * (N x + (N x)⁻¹) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = N x ^ (s.re + 2) + 2 * N x ^ s.re + N x ^ (s.re - 2) := by
          rw [e1, e2, e3, e4]
          field_simp
          ring
    calc ‖h x‖ * N x ^ z.re * |Real.log (N x)| = ‖h x‖ * (N x ^ z.re * |Real.log (N x)|) := by
          ring
      _ ≤ bound x := mul_le_mul_of_nonneg_left key (norm_nonneg _)
  · have := ((hint (s.re + 2)).add ((hint s.re).const_mul 2)).add (hint (s.re - 2))
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [bound, Pi.add_apply]
    ring
  · refine (ae_restrict_mem hS).mono fun x hx z _ => ?_
    have hx0 : (N x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hpos x hx).ne'
    have := ((hasDerivAt_id z).const_cpow (c := (N x : ℂ)) (Or.inl hx0)).const_mul (h x)
    simp only [id, mul_one] at this
    rw [Complex.ofReal_log (hpos x hx).le]
    exact this.congr_deriv (by ring)

theorem integrableOn_mul_cpow {S : Set X} (hS : MeasurableSet S) {N : X → ℝ}
    (hN : Measurable N) (hpos : ∀ x ∈ S, 0 < N x) {h : X → ℂ}
    (hmeas : AEStronglyMeasurable h (μ.restrict S)) {z : ℂ}
    (hint : IntegrableOn (fun x => ‖h x‖ * N x ^ z.re) S μ) :
    IntegrableOn (fun x => h x * (N x : ℂ) ^ z) S μ := by
  refine Integrable.mono' hint
    (hmeas.mul ((Complex.measurable_ofReal.comp hN).pow_const z).aestronglyMeasurable) ?_
  refine (ae_restrict_mem hS).mono fun x hx => ?_
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hpos x hx) z]

theorem differentiable_setIntegral_mul_cpow {S : Set X} (hS : MeasurableSet S) {N : X → ℝ}
    (hN : Measurable N) (hpos : ∀ x ∈ S, 0 < N x) {h : X → ℂ}
    (hmeas : AEStronglyMeasurable h (μ.restrict S))
    (hint : ∀ σ : ℝ, IntegrableOn (fun x => ‖h x‖ * N x ^ σ) S μ) :
    Differentiable ℂ (fun z : ℂ => ∫ x in S, h x * (N x : ℂ) ^ z ∂μ) := fun s =>
  (hasDerivAt_setIntegral_mul_cpow μ hS hN hpos hmeas hint s).differentiableAt

end Holomorphy

/-! ### Dyadic cones -/

/-- A measurable cone `C` in a finite-dimensional real vector space together with a positive
function `N` on it which is homogeneous of degree `dim E` for positive scalars. -/
structure DyadicCone (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] where
  /-- The norm-like function. -/
  N : E → ℝ
  /-- The cone. -/
  C : Set E
  measurable_N : Measurable N
  measurableSet_C : MeasurableSet C
  pos : ∀ x ∈ C, 0 < N x
  smul_mem : ∀ x ∈ C, ∀ t : ℝ, 0 < t → t • x ∈ C
  N_smul : ∀ x ∈ C, ∀ t : ℝ, 0 < t → N (t • x) = t ^ finrank ℝ E * N x
  rank_pos : 0 < finrank ℝ E

namespace DyadicCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  (D : DyadicCone E)

lemma zpow_smul_mem {x : E} (hx : x ∈ D.C) (k : ℤ) : (2 : ℝ) ^ k • x ∈ D.C :=
  D.smul_mem x hx _ (zpow_pos two_pos k)

lemma N_zpow_smul {x : E} (hx : x ∈ D.C) (k : ℤ) :
    D.N ((2 : ℝ) ^ k • x) = ((2 : ℝ) ^ k) ^ finrank ℝ E * D.N x :=
  D.N_smul x hx _ (zpow_pos two_pos k)

lemma mem_of_zpow_smul_mem {x : E} {k : ℤ} (h : (2 : ℝ) ^ k • x ∈ D.C) : x ∈ D.C := by
  have := D.zpow_smul_mem h (-k)
  rwa [smul_smul, ← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero, one_smul] at this

/-- The dyadic level `⌈log₂ N(x) / dim E⌉` of a point. -/
def level (x : E) : ℤ := ⌈Real.log (D.N x) / (finrank ℝ E * Real.log 2)⌉

include D in
lemma finrank_mul_log_two_pos : 0 < (finrank ℝ E : ℝ) * Real.log 2 :=
  mul_pos (Nat.cast_pos.mpr D.rank_pos) (Real.log_pos one_lt_two)

lemma level_zpow_smul {x : E} (hx : x ∈ D.C) (k : ℤ) :
    D.level ((2 : ℝ) ^ k • x) = D.level x + k := by
  have hn := D.finrank_mul_log_two_pos.ne'
  have hn' : (finrank ℝ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr D.rank_pos.ne'
  unfold level
  rw [D.N_zpow_smul hx, Real.log_mul (by positivity) (D.pos x hx).ne', Real.log_pow,
    Real.log_zpow, ← Int.ceil_add_intCast]
  congr 1
  field_simp
  ring

lemma level_nonpos_iff {x : E} (hx : x ∈ D.C) : D.level x ≤ 0 ↔ D.N x ≤ 1 := by
  unfold level
  rw [show (0 : ℤ) = ((0 : ℤ) : ℤ) from rfl, Int.ceil_le, Int.cast_zero,
    div_le_iff₀ D.finrank_mul_log_two_pos, zero_mul, Real.log_nonpos_iff (D.pos x hx).le]

lemma measurable_level : Measurable D.level :=
  Int.measurable_ceil.comp ((Real.measurable_log.comp D.measurable_N).div_const _)

/-- The dyadic shell of level `k`: points of the cone with `2^(n(k-1)) < N ≤ 2^(nk)`. -/
def piece (k : ℤ) : Set E := {x | x ∈ D.C ∧ D.level x = k}

lemma measurableSet_piece (k : ℤ) : MeasurableSet (D.piece k) :=
  D.measurableSet_C.inter (D.measurable_level (measurableSet_singleton k))

lemma zpow_smul_mem_piece_iff (k j : ℤ) (y : E) :
    (2 : ℝ) ^ k • y ∈ D.piece (j + k) ↔ y ∈ D.piece j := by
  constructor
  · rintro ⟨h1, h2⟩
    have hy := D.mem_of_zpow_smul_mem h1
    refine ⟨hy, ?_⟩
    rw [D.level_zpow_smul hy] at h2
    linarith
  · rintro ⟨h1, h2⟩
    exact ⟨D.zpow_smul_mem h1 k, by rw [D.level_zpow_smul h1, h2]⟩

lemma pairwise_disjoint_piece : Pairwise (Function.onFun Disjoint D.piece) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  rintro x ⟨_, hx⟩ ⟨_, hx'⟩
  exact hij (hx.symm.trans hx')

lemma bounds_of_mem_piece_zero {x : E} (hx : x ∈ D.piece 0) :
    -((finrank ℝ E : ℝ) * Real.log 2) < Real.log (D.N x) ∧ Real.log (D.N x) ≤ 0 := by
  have h := (Int.ceil_eq_iff.mp hx.2)
  have hn := D.finrank_mul_log_two_pos
  simp only [Int.cast_zero, zero_sub] at h
  rw [lt_div_iff₀ hn, div_le_iff₀ hn] at h
  constructor <;> linarith [h.1, h.2]

/-- The part of the cone where `N ≤ 1`. -/
def lower : Set E := {x | x ∈ D.C ∧ D.N x ≤ 1}

/-- The part of the cone where `N > 1`. -/
def upper : Set E := {x | x ∈ D.C ∧ 1 < D.N x}

lemma measurableSet_lower : MeasurableSet D.lower :=
  D.measurableSet_C.inter (measurableSet_le D.measurable_N measurable_const)

lemma measurableSet_upper : MeasurableSet D.upper :=
  D.measurableSet_C.inter (measurableSet_lt measurable_const D.measurable_N)

lemma lower_eq_iUnion : D.lower = ⋃ j : ℕ, D.piece (-(j : ℤ)) := by
  ext x
  simp only [lower, piece, mem_ofPred_eq, mem_iUnion]
  constructor
  · rintro ⟨hx, h1⟩
    refine ⟨(-D.level x).toNat, hx, ?_⟩
    have := (D.level_nonpos_iff hx).mpr h1
    rw [Int.toNat_of_nonneg (by linarith)]
    ring
  · rintro ⟨j, hx, h⟩
    exact ⟨hx, (D.level_nonpos_iff hx).mp (by rw [h]; simp)⟩

lemma upper_eq_iUnion : D.upper = ⋃ j : ℕ, D.piece ((j : ℤ) + 1) := by
  ext x
  simp only [upper, piece, mem_ofPred_eq, mem_iUnion]
  constructor
  · rintro ⟨hx, h1⟩
    have : ¬ D.level x ≤ 0 := fun h => absurd ((D.level_nonpos_iff hx).mp h) (not_le.mpr h1)
    refine ⟨(D.level x - 1).toNat, hx, ?_⟩
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  · rintro ⟨j, hx, h⟩
    refine ⟨hx, ?_⟩
    by_contra h'
    have := (D.level_nonpos_iff hx).mpr (not_lt.mp h')
    omega

lemma lower_union_upper : D.lower ∪ D.upper = D.C := by
  ext x
  simp only [lower, upper, mem_union, mem_ofPred_eq]
  constructor
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  · intro hx
    rcases le_or_gt (D.N x) 1 with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩

lemma disjoint_lower_upper : Disjoint D.lower D.upper := by
  rw [Set.disjoint_left]
  rintro x ⟨_, h1⟩ ⟨_, h2⟩
  linarith

lemma lower_subset : D.lower ⊆ D.C := fun _ hx => hx.1

lemma upper_subset : D.upper ⊆ D.C := fun _ hx => hx.1

/-- Data for the Mellin functional equation on a dyadic cone: a character-like function `χ`
with `χ (2 • x) = l χ x`, two functions `f` and `g` related by
`f x + A = N(x)⁻¹ (g x + B)` on the cone (the shape of a theta relation obtained from Poisson
summation), with `f χ` rapidly decreasing at the top of the cone and `g χ` at its bottom. -/
structure ThetaData (μ : Measure E) where
  /-- The character-like weight. -/
  χ : E → ℂ
  /-- The multiplier of `χ` under doubling. -/
  l : ℂ
  l_ne_zero : l ≠ 0
  χ_two_smul : ∀ x ∈ D.C, χ ((2 : ℝ) • x) = l * χ x
  integrableOn_χ : IntegrableOn χ (D.piece 0) μ
  /-- The theta function without its constant term. -/
  f : E → ℂ
  /-- The dual theta function (at the inverse point) without its constant term. -/
  g : E → ℂ
  /-- The constant term of `f`. -/
  A : ℂ
  /-- The constant term of `g`. -/
  B : ℂ
  f_add : ∀ x ∈ D.C, f x + A = (D.N x : ℂ)⁻¹ * (g x + B)
  aestronglyMeasurable_f : AEStronglyMeasurable (fun x => f x * χ x) (μ.restrict D.upper)
  aestronglyMeasurable_g : AEStronglyMeasurable (fun x => g x * χ x) (μ.restrict D.lower)
  integrableOn_f : ∀ σ : ℝ, IntegrableOn (fun x => ‖f x * χ x‖ * D.N x ^ σ) D.upper μ
  integrableOn_g : ∀ σ : ℝ, IntegrableOn (fun x => ‖g x * χ x‖ * D.N x ^ σ) D.lower μ

/-! ### Scaling of integrals over the shells -/

variable [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
  [μ.IsAddHaarMeasure]

omit [BorelSpace E] [FiniteDimensional ℝ E] in
lemma indicator_piece_zpow_smul {F : Type*} [Zero F] (h : E → F) (k : ℤ) :
    (fun y => (D.piece k).indicator h ((2 : ℝ) ^ k • y)) =
      (D.piece 0).indicator (fun y => h ((2 : ℝ) ^ k • y)) := by
  ext y
  have := D.zpow_smul_mem_piece_iff k 0 y
  rw [zero_add] at this
  by_cases hy : y ∈ D.piece 0
  · rw [indicator_of_mem hy, indicator_of_mem (this.mpr hy)]
  · rw [indicator_of_notMem hy, indicator_of_notMem (mt this.mp hy)]

lemma setIntegral_piece {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (h : E → F)
    (k : ℤ) :
    ∫ x in D.piece k, h x ∂μ =
      ((2 : ℝ) ^ k) ^ finrank ℝ E • ∫ y in D.piece 0, h ((2 : ℝ) ^ k • y) ∂μ := by
  rw [← integral_indicator (D.measurableSet_piece k),
    ← integral_indicator (D.measurableSet_piece 0)]
  have := Measure.integral_comp_smul μ ((D.piece k).indicator h) ((2 : ℝ) ^ k)
  rw [D.indicator_piece_zpow_smul] at this
  rw [this, smul_smul, abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), one_smul]

lemma integrableOn_piece_iff {F : Type*} [NormedAddCommGroup F] (h : E → F) (k : ℤ) :
    IntegrableOn h (D.piece k) μ ↔
      IntegrableOn (fun y => h ((2 : ℝ) ^ k • y)) (D.piece 0) μ := by
  rw [← integrable_indicator_iff (D.measurableSet_piece k),
    ← integrable_indicator_iff (D.measurableSet_piece 0), ← D.indicator_piece_zpow_smul,
    integrable_comp_smul_iff μ _ (by positivity)]

/-- If `Φ (2^k • y) = c^k Φ y` on the cone, the integrals over the shells form a geometric
sequence. -/
lemma setIntegral_piece_of_scaling (Φ : E → ℂ) (c : ℂ)
    (hΦ : ∀ y ∈ D.C, ∀ k : ℤ, Φ ((2 : ℝ) ^ k • y) = c ^ k * Φ y) (k : ℤ) :
    ∫ x in D.piece k, Φ x ∂μ = ((2 : ℂ) ^ finrank ℝ E * c) ^ k * ∫ x in D.piece 0, Φ x ∂μ := by
  rw [D.setIntegral_piece μ, setIntegral_congr_fun (D.measurableSet_piece 0)
    (fun y hy => hΦ y hy.1 k), integral_const_mul, Complex.real_smul]
  push_cast
  rw [mul_zpow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm k]
  ring

lemma setIntegral_piece_of_scaling_real (Φ : E → ℝ) (c : ℝ)
    (hΦ : ∀ y ∈ D.C, ∀ k : ℤ, Φ ((2 : ℝ) ^ k • y) = c ^ k * Φ y) (k : ℤ) :
    ∫ x in D.piece k, Φ x ∂μ = ((2 : ℝ) ^ finrank ℝ E * c) ^ k * ∫ x in D.piece 0, Φ x ∂μ := by
  rw [D.setIntegral_piece μ, setIntegral_congr_fun (D.measurableSet_piece 0)
    (fun y hy => hΦ y hy.1 k), integral_const_mul, smul_eq_mul]
  rw [mul_zpow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm k]
  ring

lemma integrableOn_piece_of_scaling {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (Φ : E → F) (c : ℂ)
    (hΦ : ∀ y ∈ D.C, ∀ k : ℤ, Φ ((2 : ℝ) ^ k • y) = c ^ k • Φ y)
    (hint : IntegrableOn Φ (D.piece 0) μ) (k : ℤ) : IntegrableOn Φ (D.piece k) μ := by
  rw [D.integrableOn_piece_iff]
  exact IntegrableOn.congr_fun (f := fun y => c ^ k • Φ y) (hint.smul (c ^ k))
    (fun y hy => (hΦ y hy.1 k).symm) (D.measurableSet_piece 0)

/-- Geometric summation over the lower shells. -/
theorem integral_lower_of_scaling (Φ : E → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hΦ : ∀ y ∈ D.C, ∀ k : ℤ, Φ ((2 : ℝ) ^ k • y) = c ^ k * Φ y)
    (hint : IntegrableOn Φ (D.piece 0) μ) (hr : 1 < ‖(2 : ℂ) ^ finrank ℝ E * c‖) :
    IntegrableOn Φ D.lower μ ∧
      ∫ x in D.lower, Φ x ∂μ =
        (1 - ((2 : ℂ) ^ finrank ℝ E * c)⁻¹)⁻¹ * ∫ x in D.piece 0, Φ x ∂μ := by
  set r : ℂ := (2 : ℂ) ^ finrank ℝ E * c with hr_def
  have hr0 : r ≠ 0 := mul_ne_zero (pow_ne_zero _ two_ne_zero) hc
  have hrinv : ‖r⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hr
  have hpieces : ∀ k : ℤ, IntegrableOn Φ (D.piece k) μ :=
    D.integrableOn_piece_of_scaling μ Φ c (fun y hy k => by rw [hΦ y hy k, smul_eq_mul]) hint
  have hnormΦ : ∀ y ∈ D.C, ∀ k : ℤ, ‖Φ ((2 : ℝ) ^ k • y)‖ = ‖c‖ ^ k * ‖Φ y‖ := by
    intro y hy k
    rw [hΦ y hy k, norm_mul, norm_zpow]
  have hnorm_int : ∀ j : ℕ, ∫ x in D.piece (-(j : ℤ)), ‖Φ x‖ ∂μ =
      (‖r⁻¹‖) ^ j * ∫ x in D.piece 0, ‖Φ x‖ ∂μ := by
    intro j
    rw [D.setIntegral_piece_of_scaling_real μ (fun x => ‖Φ x‖) ‖c‖ hnormΦ, zpow_neg,
      zpow_natCast, ← inv_pow, hr_def, norm_inv, norm_mul, norm_pow, Complex.norm_ofNat]
  have hsum : Summable fun j : ℕ => ∫ x in D.piece (-(j : ℤ)), ‖Φ x‖ ∂μ := by
    simp_rw [hnorm_int]
    exact (summable_geometric_of_lt_one (norm_nonneg _) hrinv).mul_right _
  have hU : IntegrableOn Φ D.lower μ := by
    rw [D.lower_eq_iUnion]
    exact integrableOn_iUnion_of_summable_integral_norm (fun j => hpieces _) hsum
  refine ⟨hU, ?_⟩
  have hU' := hU
  rw [D.lower_eq_iUnion] at hU' ⊢
  rw [integral_iUnion (s := fun j : ℕ => D.piece (-(j : ℤ))) (fun j => D.measurableSet_piece _)
    (fun i j hij => D.pairwise_disjoint_piece (by simpa using hij)) hU']
  have hk : ∀ j : ℕ, ∫ x in D.piece (-(j : ℤ)), Φ x ∂μ =
      r⁻¹ ^ j * ∫ x in D.piece 0, Φ x ∂μ := by
    intro j
    rw [D.setIntegral_piece_of_scaling μ Φ c hΦ, ← hr_def, zpow_neg, zpow_natCast, ← inv_pow]
  rw [tsum_congr hk, tsum_mul_right, tsum_geometric_of_norm_lt_one hrinv]

/-- Geometric summation over the upper shells. -/
theorem integral_upper_of_scaling (Φ : E → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hΦ : ∀ y ∈ D.C, ∀ k : ℤ, Φ ((2 : ℝ) ^ k • y) = c ^ k * Φ y)
    (hint : IntegrableOn Φ (D.piece 0) μ) (hr : ‖(2 : ℂ) ^ finrank ℝ E * c‖ < 1) :
    IntegrableOn Φ D.upper μ ∧
      ∫ x in D.upper, Φ x ∂μ =
        -(1 - ((2 : ℂ) ^ finrank ℝ E * c)⁻¹)⁻¹ * ∫ x in D.piece 0, Φ x ∂μ := by
  set r : ℂ := (2 : ℂ) ^ finrank ℝ E * c with hr_def
  have hr0 : r ≠ 0 := mul_ne_zero (pow_ne_zero _ two_ne_zero) hc
  have hr1 : r ≠ 1 := fun h => by rw [h, norm_one] at hr; exact lt_irrefl _ hr
  have hpieces : ∀ k : ℤ, IntegrableOn Φ (D.piece k) μ :=
    D.integrableOn_piece_of_scaling μ Φ c (fun y hy k => by rw [hΦ y hy k, smul_eq_mul]) hint
  have hnormΦ : ∀ y ∈ D.C, ∀ k : ℤ, ‖Φ ((2 : ℝ) ^ k • y)‖ = ‖c‖ ^ k * ‖Φ y‖ := by
    intro y hy k
    rw [hΦ y hy k, norm_mul, norm_zpow]
  have hnorm_int : ∀ j : ℕ, ∫ x in D.piece ((j : ℤ) + 1), ‖Φ x‖ ∂μ =
      ‖r‖ * (‖r‖ ^ j * ∫ x in D.piece 0, ‖Φ x‖ ∂μ) := by
    intro j
    rw [D.setIntegral_piece_of_scaling_real μ (fun x => ‖Φ x‖) ‖c‖ hnormΦ,
      zpow_add_one₀ (by positivity), zpow_natCast, hr_def, norm_mul, norm_pow,
      Complex.norm_ofNat]
    ring
  have hsum : Summable fun j : ℕ => ∫ x in D.piece ((j : ℤ) + 1), ‖Φ x‖ ∂μ := by
    simp_rw [hnorm_int]
    exact ((summable_geometric_of_lt_one (norm_nonneg _) hr).mul_right _).mul_left _
  have hU : IntegrableOn Φ D.upper μ := by
    rw [D.upper_eq_iUnion]
    exact integrableOn_iUnion_of_summable_integral_norm (fun j => hpieces _) hsum
  refine ⟨hU, ?_⟩
  have hU' := hU
  rw [D.upper_eq_iUnion] at hU' ⊢
  rw [integral_iUnion (s := fun j : ℕ => D.piece ((j : ℤ) + 1))
    (fun j => D.measurableSet_piece _)
    (fun i j hij => D.pairwise_disjoint_piece (by simpa using hij)) hU']
  have hk : ∀ j : ℕ, ∫ x in D.piece ((j : ℤ) + 1), Φ x ∂μ =
      r * (r ^ j * ∫ x in D.piece 0, Φ x ∂μ) := by
    intro j
    rw [D.setIntegral_piece_of_scaling μ Φ c hΦ, ← hr_def, zpow_add_one₀ hr0, zpow_natCast]
    ring
  rw [tsum_congr hk, tsum_mul_left, tsum_mul_right, tsum_geometric_of_norm_lt_one hr]
  have h1 : (1 - r) ≠ 0 := sub_ne_zero.mpr hr1.symm
  have h2 : (1 - r⁻¹) ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => hr1 (inv_eq_one.mp h.symm)
  field_simp
  ring

/-! ### Integrability on the first shell -/

omit [BorelSpace E] [FiniteDimensional ℝ E] in
lemma rpow_le_of_mem_piece_zero {x : E} (hx : x ∈ D.piece 0) (σ : ℝ) :
    D.N x ^ σ ≤ Real.exp (|σ| * ((finrank ℝ E : ℝ) * Real.log 2)) := by
  obtain ⟨h1, h2⟩ := D.bounds_of_mem_piece_zero hx
  rw [Real.rpow_def_of_pos (D.pos x hx.1)]
  apply Real.exp_le_exp.mpr
  have hb : |Real.log (D.N x)| ≤ (finrank ℝ E : ℝ) * Real.log 2 :=
    abs_le.mpr ⟨h1.le, h2.trans D.finrank_mul_log_two_pos.le⟩
  calc Real.log (D.N x) * σ ≤ |Real.log (D.N x) * σ| := le_abs_self _
    _ = |Real.log (D.N x)| * |σ| := abs_mul _ _
    _ ≤ ((finrank ℝ E : ℝ) * Real.log 2) * |σ| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    _ = _ := mul_comm _ _

omit [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
lemma integrableOn_piece_zero_norm_mul_rpow {h : E → ℂ} (hh : IntegrableOn h (D.piece 0) μ)
    (σ : ℝ) : IntegrableOn (fun x => ‖h x‖ * D.N x ^ σ) (D.piece 0) μ := by
  refine Integrable.mono' (hh.norm.mul_const (Real.exp (|σ| * ((finrank ℝ E : ℝ) * Real.log 2))))
    (hh.norm.aestronglyMeasurable.mul (D.measurable_N.pow_const σ).aestronglyMeasurable) ?_
  refine (ae_restrict_mem (D.measurableSet_piece 0)).mono fun x hx => ?_
  rw [norm_mul, norm_norm, Real.norm_of_nonneg (Real.rpow_nonneg (D.pos x hx.1).le _)]
  exact mul_le_mul_of_nonneg_left (D.rpow_le_of_mem_piece_zero hx σ) (norm_nonneg _)

/-! ### Complex powers of `N` under doubling -/

omit [BorelSpace E] [FiniteDimensional ℝ E] in
lemma ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (x : ℂ) ^ z = Complex.exp (Real.log x * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le]

omit [BorelSpace E] [FiniteDimensional ℝ E] in
lemma two_zpow_pow_cpow (k : ℤ) (n : ℕ) (z : ℂ) :
    ((((2 : ℝ) ^ k) ^ n : ℝ) : ℂ) ^ z = ((2 : ℂ) ^ ((n : ℂ) * z)) ^ k := by
  have hlog : Complex.log 2 = (Real.log 2 : ℂ) := by
    rw [Complex.ofReal_log zero_le_two, Complex.ofReal_ofNat]
  rw [ofReal_cpow_eq_exp (by positivity), Complex.cpow_def_of_ne_zero two_ne_zero,
    ← Complex.exp_int_mul, Real.log_pow, Real.log_zpow, hlog]
  congr 1
  push_cast
  ring

omit [BorelSpace E] [FiniteDimensional ℝ E] in
lemma N_cpow_zpow_smul (z : ℂ) {y : E} (hy : y ∈ D.C) (k : ℤ) :
    (D.N ((2 : ℝ) ^ k • y) : ℂ) ^ z =
      ((2 : ℂ) ^ ((finrank ℝ E : ℂ) * z)) ^ k * (D.N y : ℂ) ^ z := by
  rw [D.N_zpow_smul hy, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (D.pos y hy).le, two_zpow_pow_cpow]

/-! ### The Mellin functional equation -/

namespace ThetaData

variable {D μ} (T : D.ThetaData μ)

omit [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
lemma χ_pow_smul {x : E} (hx : x ∈ D.C) (m : ℕ) :
    T.χ ((2 : ℝ) ^ m • x) = T.l ^ m * T.χ x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_smul, T.χ_two_smul _ (D.smul_mem x hx _ (by positivity)), ih]
    ring

omit [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
lemma χ_zpow_smul {x : E} (hx : x ∈ D.C) (k : ℤ) :
    T.χ ((2 : ℝ) ^ k • x) = T.l ^ k * T.χ x := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simpa using T.χ_pow_smul hx m
  · have hy := D.zpow_smul_mem hx (-(m : ℤ))
    have := T.χ_pow_smul hy m
    rw [smul_smul, ← zpow_natCast, ← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero,
      one_smul] at this
    rw [this, zpow_neg T.l (m : ℤ), zpow_natCast,
      inv_mul_cancel_left₀ (pow_ne_zero _ T.l_ne_zero)]

/-- The ratio `l 2^(n w)` of the integrals of `χ N^(w-1)` over consecutive shells. -/
def ratio (w : ℂ) : ℂ := T.l * (2 : ℂ) ^ ((finrank ℝ E : ℂ) * w)

/-- The integral of `χ N^(w-1)` over the shell `2^(-n) < N ≤ 1`. -/
def J (w : ℂ) : ℂ := ∫ x in D.piece 0, T.χ x * (D.N x : ℂ) ^ (w - 1) ∂μ

/-- The geometric sum of the shell integrals: `∫_{N ≤ 1} χ N^(w-1)` when this converges, and
minus `∫_{N > 1} χ N^(w-1)` when that converges. -/
def Itilde (w : ℂ) : ℂ := (1 - (T.ratio w)⁻¹)⁻¹ * T.J w

/-- The integral of `f χ N^(s-1)` over the part `N > 1` of the cone. -/
def E1 (s : ℂ) : ℂ := ∫ x in D.upper, T.f x * T.χ x * (D.N x : ℂ) ^ (s - 1) ∂μ

/-- The integral of `g χ N^(s-2)` over the part `N ≤ 1` of the cone. -/
def E2 (s : ℂ) : ℂ := ∫ x in D.lower, T.g x * T.χ x * (D.N x : ℂ) ^ (s - 2) ∂μ

/-- The meromorphic continuation of `∫_C f χ N^(s-1)`. -/
def M (s : ℂ) : ℂ := T.E1 s + T.E2 s + T.B * T.Itilde (s - 1) - T.A * T.Itilde s

omit [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
lemma scaling (w : ℂ) {y : E} (hy : y ∈ D.C) (k : ℤ) :
    T.χ ((2 : ℝ) ^ k • y) * (D.N ((2 : ℝ) ^ k • y) : ℂ) ^ (w - 1) =
      (T.l * (2 : ℂ) ^ ((finrank ℝ E : ℂ) * (w - 1))) ^ k *
        (T.χ y * (D.N y : ℂ) ^ (w - 1)) := by
  rw [T.χ_zpow_smul hy, D.N_cpow_zpow_smul _ hy, mul_zpow]
  ring

omit [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
lemma two_pow_mul_eq_ratio (w : ℂ) :
    (2 : ℂ) ^ finrank ℝ E * (T.l * (2 : ℂ) ^ ((finrank ℝ E : ℂ) * (w - 1))) = T.ratio w := by
  rw [ratio, ← Complex.cpow_natCast, mul_left_comm, ← Complex.cpow_add _ _ two_ne_zero]
  congr 2
  ring

omit [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
lemma norm_ratio (w : ℂ) : ‖T.ratio w‖ = ‖T.l‖ * 2 ^ ((finrank ℝ E : ℝ) * w.re) := by
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [ratio, norm_mul, h2, Complex.norm_cpow_eq_rpow_re_of_pos two_pos]
  congr 2
  simp

omit [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
lemma norm_ratio_le {w w' : ℂ} (h : w.re ≤ w'.re) : ‖T.ratio w‖ ≤ ‖T.ratio w'‖ := by
  rw [T.norm_ratio, T.norm_ratio]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le one_le_two
    (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))) (norm_nonneg _)

omit [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- In a right half-plane both convergence conditions of the functional equation hold. -/
lemma exists_re_gt :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → 1 < ‖T.ratio (s - 1)‖ ∧ ‖T.ratio (1 - s)‖ < 1 := by
  have hl : 0 < ‖T.l‖ := norm_pos_iff.mpr T.l_ne_zero
  have hn : (0 : ℝ) < finrank ℝ E := Nat.cast_pos.mpr D.rank_pos
  set lam : ℝ := Real.log ‖T.l‖ / Real.log 2
  have hlam : ‖T.l‖ = (2 : ℝ) ^ lam := by
    rw [Real.rpow_def_of_pos two_pos, mul_div_cancel₀ _ (Real.log_pos one_lt_two).ne',
      Real.exp_log hl]
  refine ⟨1 + |lam| / finrank ℝ E, fun s hs => ?_⟩
  have key : |lam| < (finrank ℝ E : ℝ) * (s.re - 1) :=
    (div_lt_iff₀' hn).mp (by linarith)
  rw [T.norm_ratio, T.norm_ratio, hlam, ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
  have h1 := neg_abs_le lam
  have h2 := le_abs_self lam
  simp only [Complex.sub_re, Complex.one_re]
  constructor
  · apply Real.one_lt_rpow one_lt_two
    linarith
  · apply Real.rpow_lt_one_of_one_lt_of_neg one_lt_two
    linarith

omit [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
lemma ratio_differentiable : Differentiable ℂ T.ratio :=
  (((differentiable_const _).mul differentiable_id).const_cpow (Or.inl two_ne_zero)).const_mul _

omit [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
lemma integrableOn_piece_zero (w : ℂ) :
    IntegrableOn (fun x => T.χ x * (D.N x : ℂ) ^ (w - 1)) (D.piece 0) μ :=
  integrableOn_mul_cpow μ (D.measurableSet_piece 0) D.measurable_N (fun x hx => D.pos x hx.1)
    T.integrableOn_χ.aestronglyMeasurable
    (D.integrableOn_piece_zero_norm_mul_rpow μ T.integrableOn_χ _)

omit [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
lemma J_differentiable : Differentiable ℂ T.J :=
  (differentiable_setIntegral_mul_cpow μ (D.measurableSet_piece 0) D.measurable_N
    (fun x hx => D.pos x hx.1) T.integrableOn_χ.aestronglyMeasurable
    (D.integrableOn_piece_zero_norm_mul_rpow μ T.integrableOn_χ)).comp
    (differentiable_id.sub_const 1)

omit [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
lemma E1_differentiable : Differentiable ℂ T.E1 :=
  (differentiable_setIntegral_mul_cpow μ D.measurableSet_upper D.measurable_N
    (fun x hx => D.pos x hx.1) T.aestronglyMeasurable_f T.integrableOn_f).comp
    (differentiable_id.sub_const 1)

omit [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
lemma E2_differentiable : Differentiable ℂ T.E2 :=
  (differentiable_setIntegral_mul_cpow μ D.measurableSet_lower D.measurable_N
    (fun x hx => D.pos x hx.1) T.aestronglyMeasurable_g T.integrableOn_g).comp
    (differentiable_id.sub_const 2)

omit [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
lemma integrableOn_upper_f (z : ℂ) :
    IntegrableOn (fun x => T.f x * T.χ x * (D.N x : ℂ) ^ z) D.upper μ :=
  integrableOn_mul_cpow μ D.measurableSet_upper D.measurable_N (fun x hx => D.pos x hx.1)
    T.aestronglyMeasurable_f (T.integrableOn_f _)

omit [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
lemma integrableOn_lower_g (z : ℂ) :
    IntegrableOn (fun x => T.g x * T.χ x * (D.N x : ℂ) ^ z) D.lower μ :=
  integrableOn_mul_cpow μ D.measurableSet_lower D.measurable_N (fun x hx => D.pos x hx.1)
    T.aestronglyMeasurable_g (T.integrableOn_g _)

omit [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
lemma ratio_param_ne_zero (w : ℂ) : T.l * (2 : ℂ) ^ ((finrank ℝ E : ℂ) * (w - 1)) ≠ 0 :=
  mul_ne_zero T.l_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero))

/-- Below the cone's unit level, `∫ χ N^(w-1)` is the geometric sum `Itilde w`. -/
theorem lower_integral {w : ℂ} (hw : 1 < ‖T.ratio w‖) :
    IntegrableOn (fun x => T.χ x * (D.N x : ℂ) ^ (w - 1)) D.lower μ ∧
      ∫ x in D.lower, T.χ x * (D.N x : ℂ) ^ (w - 1) ∂μ = T.Itilde w := by
  rw [← T.two_pow_mul_eq_ratio] at hw
  have := D.integral_lower_of_scaling μ _ _ (T.ratio_param_ne_zero w)
    (fun y hy k => T.scaling w hy k) (T.integrableOn_piece_zero w) hw
  rwa [T.two_pow_mul_eq_ratio] at this

/-- Above the cone's unit level, `∫ χ N^(w-1)` is `- Itilde w`. -/
theorem upper_integral {w : ℂ} (hw : ‖T.ratio w‖ < 1) :
    IntegrableOn (fun x => T.χ x * (D.N x : ℂ) ^ (w - 1)) D.upper μ ∧
      ∫ x in D.upper, T.χ x * (D.N x : ℂ) ^ (w - 1) ∂μ = -T.Itilde w := by
  rw [← T.two_pow_mul_eq_ratio] at hw
  have := D.integral_upper_of_scaling μ _ _ (T.ratio_param_ne_zero w)
    (fun y hy k => T.scaling w hy k) (T.integrableOn_piece_zero w) hw
  rw [T.two_pow_mul_eq_ratio] at this
  refine ⟨this.1, ?_⟩
  rw [this.2, Itilde, neg_mul, J]

omit [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- `M` is meromorphic on the whole plane. -/
theorem meromorphicOn_M : MeromorphicOn T.M univ := by
  intro x _
  have key : ∀ φ ψ : ℂ → ℂ, Differentiable ℂ φ → Differentiable ℂ ψ →
      MeromorphicAt (fun s => (1 - (ψ s)⁻¹)⁻¹ * φ s) x := fun φ ψ hφ hψ =>
    (((MeromorphicAt.const 1 x).sub (hψ.analyticAt x).meromorphicAt.inv).inv).mul
      (hφ.analyticAt x).meromorphicAt
  have h1 : MeromorphicAt (fun s => T.Itilde (s - 1)) x :=
    key _ _ (T.J_differentiable.comp (differentiable_id.sub_const 1))
      (T.ratio_differentiable.comp (differentiable_id.sub_const 1))
  have h0 : MeromorphicAt T.Itilde x := key _ _ T.J_differentiable T.ratio_differentiable
  exact ((((T.E1_differentiable.analyticAt x).meromorphicAt.add
    (T.E2_differentiable.analyticAt x).meromorphicAt).add
      ((MeromorphicAt.const T.B x).mul h1)).sub ((MeromorphicAt.const T.A x).mul h0))

omit [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
lemma cpow_sub_one_eq {y : ℝ} (hy : 0 < y) (z : ℂ) :
    (y : ℂ) ^ (z - 1) = (y : ℂ) ^ z / y := by
  rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hy.ne'), Complex.cpow_one]

/-- For `Re s` large, `M s` is the Mellin integral `∫_C f χ N^(s-1)`. -/
theorem M_eq_integral {s : ℂ} (hs : 1 < ‖T.ratio (s - 1)‖) :
    IntegrableOn (fun x => T.f x * T.χ x * (D.N x : ℂ) ^ (s - 1)) D.C μ ∧
      T.M s = ∫ x in D.C, T.f x * T.χ x * (D.N x : ℂ) ^ (s - 1) ∂μ := by
  have hs' : 1 < ‖T.ratio s‖ := hs.trans_le (T.norm_ratio_le (by simp))
  obtain ⟨hI1, hJ1⟩ := T.lower_integral hs
  obtain ⟨hI0, hJ0⟩ := T.lower_integral hs'
  have hup := T.integrableOn_upper_f (s - 1)
  have hg := T.integrableOn_lower_g (s - 2)
  have heq : EqOn (fun x => T.f x * T.χ x * (D.N x : ℂ) ^ (s - 1))
      (fun x => T.g x * T.χ x * (D.N x : ℂ) ^ (s - 2) +
        (T.B * (T.χ x * (D.N x : ℂ) ^ (s - 1 - 1)) - T.A * (T.χ x * (D.N x : ℂ) ^ (s - 1))))
      D.lower := by
    intro x hx
    have hN0 := D.pos x hx.1
    have hN : (D.N x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN0.ne'
    have hf : T.f x = (D.N x : ℂ)⁻¹ * (T.g x + T.B) - T.A := eq_sub_of_add_eq (T.f_add x hx.1)
    have e1 : (D.N x : ℂ) ^ (s - 2) = (D.N x : ℂ) ^ (s - 1) / D.N x := by
      rw [show s - 2 = s - 1 - 1 by ring, cpow_sub_one_eq hN0]
    simp only
    rw [hf, cpow_sub_one_eq hN0 (s - 1), e1]
    field_simp
    ring
  have hBA : IntegrableOn (fun x => T.B * (T.χ x * (D.N x : ℂ) ^ (s - 1 - 1)) -
      T.A * (T.χ x * (D.N x : ℂ) ^ (s - 1))) D.lower μ :=
    (hI1.const_mul T.B).sub (hI0.const_mul T.A)
  have hlow : IntegrableOn (fun x => T.f x * T.χ x * (D.N x : ℂ) ^ (s - 1)) D.lower μ :=
    (hg.add hBA).congr_fun heq.symm D.measurableSet_lower
  refine ⟨by rw [← D.lower_union_upper]; exact hlow.union hup, ?_⟩
  rw [← D.lower_union_upper, setIntegral_union D.disjoint_lower_upper D.measurableSet_upper hlow hup,
    setIntegral_congr_fun D.measurableSet_lower heq, integral_add hg hBA,
    integral_sub (hI1.const_mul T.B) (hI0.const_mul T.A), integral_const_mul, integral_const_mul,
    hJ1, hJ0]
  simp only [M, E1, E2]
  ring

/-- For `Re s` large, `M (1 - s)` is the dual Mellin integral `∫_C g χ N^(-s-1)`. -/
theorem M_one_sub_eq_integral {s : ℂ} (hs : ‖T.ratio (1 - s)‖ < 1) :
    IntegrableOn (fun x => T.g x * T.χ x * (D.N x : ℂ) ^ (-s - 1)) D.C μ ∧
      T.M (1 - s) = ∫ x in D.C, T.g x * T.χ x * (D.N x : ℂ) ^ (-s - 1) ∂μ := by
  have hs' : ‖T.ratio (-s)‖ < 1 := (T.norm_ratio_le (by simp)).trans_lt hs
  obtain ⟨hI1, hJ1⟩ := T.upper_integral hs
  obtain ⟨hI0, hJ0⟩ := T.upper_integral hs'
  have hup := T.integrableOn_upper_f (1 - s - 1)
  have hg := T.integrableOn_lower_g (-s - 1)
  have heq : EqOn (fun x => T.g x * T.χ x * (D.N x : ℂ) ^ (-s - 1))
      (fun x => T.f x * T.χ x * (D.N x : ℂ) ^ (1 - s - 1) +
        (T.A * (T.χ x * (D.N x : ℂ) ^ (1 - s - 1)) - T.B * (T.χ x * (D.N x : ℂ) ^ (-s - 1))))
      D.upper := by
    intro x hx
    have hN0 := D.pos x hx.1
    have hN : (D.N x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN0.ne'
    have hg' : T.g x = (D.N x : ℂ) * (T.f x + T.A) - T.B := by
      rw [T.f_add x hx.1]
      field_simp
      ring
    have e1 : (D.N x : ℂ) ^ (-s - 1) = (D.N x : ℂ) ^ (1 - s - 1) / D.N x := by
      rw [show 1 - s - 1 = -s by ring, cpow_sub_one_eq hN0]
    simp only
    rw [hg', e1]
    field_simp
    ring
  have hAB : IntegrableOn (fun x => T.A * (T.χ x * (D.N x : ℂ) ^ (1 - s - 1)) -
      T.B * (T.χ x * (D.N x : ℂ) ^ (-s - 1))) D.upper μ :=
    (hI1.const_mul T.A).sub (hI0.const_mul T.B)
  have hupg : IntegrableOn (fun x => T.g x * T.χ x * (D.N x : ℂ) ^ (-s - 1)) D.upper μ :=
    (hup.add hAB).congr_fun heq.symm D.measurableSet_upper
  refine ⟨by rw [← D.lower_union_upper]; exact hg.union hupg, ?_⟩
  rw [← D.lower_union_upper, setIntegral_union D.disjoint_lower_upper D.measurableSet_upper hg hupg,
    setIntegral_congr_fun D.measurableSet_upper heq, integral_add hup hAB,
    integral_sub (hI1.const_mul T.A) (hI0.const_mul T.B), integral_const_mul, integral_const_mul,
    hJ1, hJ0]
  simp only [M, E1, E2, show (1 : ℂ) - s - 2 = -s - 1 by ring, show (1 : ℂ) - s - 1 = -s by ring]
  ring

end ThetaData

end DyadicCone

end Langlands.Global.Hecke

end
