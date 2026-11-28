import Langlands.Global.RankinSelberg.RealEqualConvergence
import Langlands.Global.RankinSelberg.UnequalAnalyticPoints

/-! # Convergence and holomorphy of the real unequal-rank Rankin–Selberg integral -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealUnequalConvergence

open Langlands.Archimedean (unitaryCompact)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Langlands.QuotientIntegration (descend)
open ArchimedeanLocal RealIwasawa RealConvergenceAnalysis RealEqualConvergence

local instance realUneqGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
local instance realUneqGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
local instance realUneqNMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
local instance realUneqNBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
local instance realUneqQMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
local instance realUneqQBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

variable {r t : ℕ}

/-! ### Padding by zeros and by the identity -/

/-- The vector `y` followed by zeros. -/
def padVec (r : ℕ) (y : Fin (t + 1) → ℝ) : Fin (r + 1) → ℝ :=
  fun j => if hj : (j : ℕ) < t + 1 then y ⟨j, hj⟩ else 0

/-- The vector `y` extended by zeros to all natural numbers. -/
def extVec (y : Fin (t + 1) → ℝ) (j : ℕ) : ℝ :=
  if hj : j < t + 1 then y ⟨j, hj⟩ else 0

theorem padVec_apply (y : Fin (t + 1) → ℝ) (j : Fin (r + 1)) :
    padVec r y j = extVec y j := rfl

theorem extVec_fin (y : Fin (t + 1) → ℝ) (j : Fin (t + 1)) : extVec y j = y j := by
  unfold extVec
  rw [dite_eq_left j.2]

theorem extVec_of_le (y : Fin (t + 1) → ℝ) {j : ℕ} (hj : t + 1 ≤ j) : extVec y j = 0 := by
  unfold extVec
  rw [dite_eq_right (by omega)]

/-- `diag(torus y, 1) = torus (y, 0)`. -/
theorem padGL_torus (hp : t + 1 ≤ r + 1) (y : Fin (t + 1) → ℝ) :
    padGL hp (torus y) = torus (padVec r y) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [UnequalAnalytic.padGL_apply]
  simp only [torus_val, Matrix.diagonal_apply]
  by_cases hij : (i : ℕ) < t + 1 ∧ (j : ℕ) < t + 1
  · rw [dite_eq_left hij]
    by_cases he : i = j
    · subst he
      rw [ite_eq_left rfl, ite_eq_left rfl, padVec_apply, ← extVec_fin y ⟨i, hij.1⟩]
    · have he' : (⟨i, hij.1⟩ : Fin (t + 1)) ≠ ⟨j, hij.2⟩ := by
        intro h'
        exact he (Fin.ext (Fin.mk.inj_iff.mp h'))
      rw [ite_eq_right he', ite_eq_right he]
  · rw [dite_eq_right hij]
    by_cases he : i = j
    · subst he
      have hi : ¬ (i : ℕ) < t + 1 := fun h' => hij ⟨h', h'⟩
      rw [Matrix.one_apply_eq, ite_eq_left rfl, padVec_apply, extVec_of_le y (not_lt.mp hi),
        Real.exp_zero]
    · rw [Matrix.one_apply_ne he, ite_eq_right he]

/-- `diag(k, 1)` is orthogonal for orthogonal `k`. -/
theorem padGL_mem_unitary (hp : t + 1 ≤ r + 1) (k : unitaryCompact ℝ (t + 1)) :
    padGL hp (k : Langlands.GeneralLinear (t + 1) ℝ) ∈ unitaryCompact ℝ (r + 1) := by
  change ((padGL hp (k : Langlands.GeneralLinear (t + 1) ℝ) : Langlands.GeneralLinear (r + 1) ℝ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) ∈ Matrix.unitaryGroup (Fin (r + 1)) ℝ
  rw [Matrix.mem_unitaryGroup_iff']
  have hst : star ((padGL hp (k : Langlands.GeneralLinear (t + 1) ℝ) :
      Langlands.GeneralLinear (r + 1) ℝ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) =
      ((padGL hp ((k : Langlands.GeneralLinear (t + 1) ℝ)⁻¹) : Langlands.GeneralLinear (r + 1) ℝ) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) := by
    ext i j
    rw [Matrix.star_apply, star_trivial, UnequalAnalytic.padGL_apply,
      UnequalAnalytic.padGL_apply, val_inv_of_mem]
    by_cases hij : (i : ℕ) < t + 1 ∧ (j : ℕ) < t + 1
    · rw [dite_eq_left ⟨hij.2, hij.1⟩, dite_eq_left hij, Matrix.transpose_apply]
    · rw [dite_eq_right (fun h' => hij ⟨h'.2, h'.1⟩), dite_eq_right hij]
      by_cases he : i = j
      · subst he
        rfl
      · rw [Matrix.one_apply_ne he, Matrix.one_apply_ne (Ne.symm he)]
  rw [hst, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

/-- `diag(k, 1)` as an element of the orthogonal group. -/
def padUnitary (hp : t + 1 ≤ r + 1) (k : unitaryCompact ℝ (t + 1)) : unitaryCompact ℝ (r + 1) :=
  ⟨padGL hp (k : Langlands.GeneralLinear (t + 1) ℝ), padGL_mem_unitary hp k⟩

/-- The positive simple-root parts of `(y, 0)`: those of `y`, plus the positive part of the last
coordinate of `y`. -/
theorem rootPos_padVec (h : t < r) (y : Fin (t + 1) → ℝ) :
    rootPos (padVec r y) = rootPos y + max (y (Fin.last t)) 0 := by
  set g : ℕ → ℝ := fun i => max (extVec y i - extVec y (i + 1)) 0 with hg
  have h1 : rootPos (padVec r y) = ∑ i ∈ Finset.range r, g i := by
    rw [← Fin.sum_univ_eq_sum_range g r]
    rfl
  have h2 : rootPos y = ∑ i ∈ Finset.range t, g i := by
    rw [← Fin.sum_univ_eq_sum_range g t]
    unfold rootPos
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hg]
    simp only
    rw [← extVec_fin y i.castSucc, ← extVec_fin y i.succ]
    rfl
  have h3 : g t = max (y (Fin.last t)) 0 := by
    rw [hg]
    simp only
    rw [extVec_of_le y (le_refl (t + 1)), sub_zero, ← extVec_fin y (Fin.last t)]
    rfl
  have h4 : ∑ i ∈ Finset.Ico (t + 1) r, g i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    rw [hg]
    simp only
    rw [extVec_of_le y hi.1, extVec_of_le y (by omega), sub_zero, max_self]
  rw [h1, h2, ← h3, ← Finset.sum_range_add_sum_Ico g (Nat.succ_le_of_lt h), h4, add_zero,
    Finset.sum_range_succ]

theorem sum_abs_padVec (h : t < r) (y : Fin (t + 1) → ℝ) :
    ∑ j, |padVec r y j| = ∑ j, |y j| := by
  set g : ℕ → ℝ := fun i => |extVec y i| with hg
  have h1 : ∑ j, |padVec r y j| = ∑ i ∈ Finset.range (r + 1), g i := by
    rw [← Fin.sum_univ_eq_sum_range g (r + 1)]
    rfl
  have h2 : ∑ j, |y j| = ∑ i ∈ Finset.range (t + 1), g i := by
    rw [← Fin.sum_univ_eq_sum_range g (t + 1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hg]
    simp only
    rw [extVec_fin y i]
  have h4 : ∑ i ∈ Finset.Ico (t + 1) (r + 1), g i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    rw [hg]
    simp only
    rw [extVec_of_le y hi.1, abs_zero]
  rw [h1, h2, ← Finset.sum_range_add_sum_Ico g (by omega : t + 1 ≤ r + 1), h4, add_zero]

/-- **The gauge estimate on `diag(g, 1)`.** If `W` on `GL_(r+1)(ℝ)` satisfies the gauge
estimate, then on `diag(torus y · k, 1)` it decays arbitrarily fast both in the positive
simple-root parts of `y` and in the positive part of the last coordinate `y_t`. -/
theorem pad_gauge {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ} (hW : HasGauge W) (h : t < r)
    (hp : t + 1 ≤ r + 1) :
    ∃ N : ℕ, ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (y : Fin (t + 1) → ℝ) (k : unitaryCompact ℝ (t + 1)),
        ‖W (padGL hp (torus y * (k : Langlands.GeneralLinear (t + 1) ℝ)))‖ ≤
          C * Real.exp (-(M : ℝ) * rootPos y + (N : ℝ) * ∑ j, |y j| -
            (M : ℝ) * max (y (Fin.last t)) 0) := by
  obtain ⟨N, hN⟩ := hW
  refine ⟨N, fun M => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN M
  refine ⟨C, hC, fun y k => ?_⟩
  have e : padGL hp (torus y * (k : Langlands.GeneralLinear (t + 1) ℝ)) =
      torus (padVec r y) *
        ((padUnitary hp k : unitaryCompact ℝ (r + 1)) : Langlands.GeneralLinear (r + 1) ℝ) := by
    rw [map_mul, padGL_torus]
    rfl
  rw [e]
  refine (hb (padVec r y) (padUnitary hp k)).trans (le_of_eq ?_)
  rw [rootPos_padVec h, sum_abs_padVec h]
  congr 2
  ring

/-! ### The Whittaker character on padded unipotent matrices -/

theorem padGL_mem_upperUnipotent (hp : t + 1 ≤ r + 1) {u : Langlands.GeneralLinear (t + 1) ℝ}
    (hu : u ∈ Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ) :
    padGL hp u ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · change ((padGL hp u : Langlands.GeneralLinear (r + 1) ℝ) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) i j = 0
    rw [UnequalAnalytic.padGL_apply]
    by_cases hij : (i : ℕ) < t + 1 ∧ (j : ℕ) < t + 1
    · rw [dite_eq_left hij]
      exact hu.1 (show (⟨j, hij.2⟩ : Fin (t + 1)) < ⟨i, hij.1⟩ from hji)
    · have hne : i ≠ j := by
        intro he
        subst he
        exact lt_irrefl _ hji
      rw [dite_eq_right hij, Matrix.one_apply_ne hne]
  · change ((padGL hp u : Langlands.GeneralLinear (r + 1) ℝ) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) i i = 1
    rw [UnequalAnalytic.padGL_apply]
    by_cases hii : (i : ℕ) < t + 1 ∧ (i : ℕ) < t + 1
    · rw [dite_eq_left hii]
      exact hu.2 _
    · rw [dite_eq_right hii, Matrix.one_apply_eq]

theorem realWhittakerCharacter_padGL (h : t < r) (hp : t + 1 ≤ r + 1) (a : ℝˣ)
    (u : Langlands.GeneralLinear (t + 1) ℝ) :
    realWhittakerCharacter a (padGL hp u) = realWhittakerCharacter a u := by
  unfold realWhittakerCharacter
  congr 1
  set g : ℕ → ℝ := fun i => if hi : i < t then
    (u : Matrix (Fin (t + 1)) (Fin (t + 1)) ℝ) ⟨i, by omega⟩ ⟨i + 1, by omega⟩ else 0 with hg
  have h1 : ∑ i : Fin r, (padGL hp u).val i.castSucc i.succ = ∑ i ∈ Finset.range r, g i := by
    rw [← Fin.sum_univ_eq_sum_range g r]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [UnequalAnalytic.padGL_apply, hg]
    simp only [Fin.val_castSucc, Fin.val_succ]
    by_cases hi : (i : ℕ) < t
    · rw [dite_eq_left (show (i : ℕ) < t + 1 ∧ (i : ℕ) + 1 < t + 1 by omega), dite_eq_left hi]
    · rw [dite_eq_right (show ¬ ((i : ℕ) < t + 1 ∧ (i : ℕ) + 1 < t + 1) by omega), dite_eq_right hi,
        Matrix.one_apply_ne]
      intro he
      have := congrArg Fin.val he
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      omega
  have h2 : ∑ i : Fin t, u.val i.castSucc i.succ = ∑ i ∈ Finset.range t, g i := by
    rw [← Fin.sum_univ_eq_sum_range g t]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hg]
    simp only
    rw [dite_eq_left i.2]
    rfl
  have h4 : ∑ i ∈ Finset.Ico t r, g i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    rw [hg]
    simp only
    rw [dite_eq_right (by omega)]
  rw [h1, h2, ← Finset.sum_range_add_sum_Ico g h.le, h4, add_zero]

/-! ### Convergence and holomorphy -/

/-- `W(diag(g, 1)) W'(g)` on `GL_(t+1)(ℝ)`. -/
def kernel (hp : t + 1 ≤ r + 1) (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ) (g : Langlands.GeneralLinear (t + 1) ℝ) : ℂ :=
  W (padGL hp g) * W' g

theorem continuous_kernel (hp : t + 1 ≤ r + 1) {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    {W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ} (hW : Continuous W) (hW' : Continuous W') :
    Continuous (kernel hp W W') :=
  (hW.comp (UnequalAnalytic.continuous_padGL hp)).mul hW'

/-- **Convergence and holomorphy of the real unequal-rank integral.** Let `t < r`, let
`W` on `GL_(r+1)(ℝ)` and `W'` on `GL_(t+1)(ℝ)` be continuous, with
`W(diag(ug, 1)) W'(ug) = W(diag(g, 1)) W'(g)` for upper unipotent `u`, and both satisfying the
gauge estimate. Then there is `σ` such that the integrand of `Ψ(s; W, W')` is integrable for
`Re s > σ` and `Ψ(·; W, W')` is holomorphic there. -/
theorem exists_convergence (h : t < r) (D : RealQuotientMeasureData t)
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ} {W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ}
    (hW : Continuous W) (hW' : Continuous W')
    (hinv : ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ, ∀ g,
      kernel (Nat.le_of_lt (Nat.succ_lt_succ h)) W W' (u * g) =
        kernel (Nat.le_of_lt (Nat.succ_lt_succ h)) W W' g)
    (hgW : HasGauge W) (hgW' : HasGauge W') :
    ∃ σ : ℝ, (∀ s : ℂ, σ < s.re → Integrable (realUnequalIntegrand h W W' s) D.measure) ∧
      DifferentiableOn ℂ (realUnequalIntegral h D W W') {s : ℂ | σ < s.re} := by
  let hp : t + 1 ≤ r + 1 := Nat.le_of_lt (Nat.succ_lt_succ h)
  obtain ⟨N1, hN1⟩ := pad_gauge hgW h hp
  obtain ⟨N2, hN2⟩ := hgW'
  obtain ⟨C2, hC2, hb2⟩ := hN2 0
  have hA : (0 : ℝ) ≤ (N1 : ℝ) + N2 := by positivity
  have hBound : HasOrdinaryToralBound ((N1 : ℝ) + N2) (kernel hp W W') := by
    intro M
    obtain ⟨C1, hC1, hb1⟩ := hN1 M
    refine ⟨C1 * C2, mul_nonneg hC1 hC2, fun y k => ?_⟩
    simp only [kernel, norm_mul]
    refine (mul_le_mul (hb1 y k) (hb2 y k) (norm_nonneg _) (by positivity)).trans_eq ?_
    simp only [Nat.cast_zero, neg_zero, zero_mul, zero_add]
    rw [show ∀ x y : ℝ, (C1 * x) * (C2 * y) = C1 * C2 * (x * y) by intros; ring, ← Real.exp_add]
    congr 2
    ring
  obtain ⟨σ, hConv⟩ := exists_convergence_of_toral_bound D hA (((r - t : ℕ) : ℝ) / 2)
  have hConv' := hConv (kernel hp W W') (continuous_kernel hp hW hW')
    (fun u g => hinv u.val u.2 g) hBound
  have he (s : ℂ) : realUnequalIntegrand h W W' s = fun q =>
      kernel hp W W' q.out * Complex.exp ((s - ((r - t : ℕ) : ℂ) / 2) * (logDet q.out : ℂ)) := rfl
  simp only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat, ← he] at hConv'
  exact ⟨σ, hConv'⟩

/-! ### Functions with uniformly regular derivatives -/

section Regular

open RealLocalWhittaker (iteratedRightDerivative regularFunctions)

set_option backward.isDefEq.respectTransparency false in
/-- **Convergence and holomorphy for uniformly regular functions.** -/
theorem exists_convergence_of_regular (h : t < r) (D : RealQuotientMeasureData t) {a : ℝˣ}
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ} {W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ}
    (hreg : ∀ Xs, iteratedRightDerivative r Xs W ∈ regularFunctions r a)
    (hgrowth : ∃ N : ℕ, ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖iteratedRightDerivative r Xs W g‖ ≤ C * realMatrixHeight g ^ N)
    (hreg' : ∀ Xs, iteratedRightDerivative t Xs W' ∈ regularFunctions t (-a))
    (hgrowth' : ∃ N : ℕ, ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖iteratedRightDerivative t Xs W' g‖ ≤ C * realMatrixHeight g ^ N) :
    ∃ σ : ℝ, (∀ s : ℂ, σ < s.re → Integrable (realUnequalIntegrand h W W' s) D.measure) ∧
      DifferentiableOn ℂ (realUnequalIntegral h D W W') {s : ℂ | σ < s.re} := by
  have hW : W ∈ regularFunctions r a := hreg []
  have hW' : W' ∈ regularFunctions t (-a) := hreg' []
  set hp : t + 1 ≤ r + 1 := Nat.le_of_lt (Nat.succ_lt_succ h) with hhp
  have hinv : ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ, ∀ g,
      kernel hp W W' (u * g) = kernel hp W W' g := by
    intro u hu g
    unfold kernel
    rw [map_mul, hW.1 _ (padGL_mem_upperUnipotent hp hu) _, hW'.1 u hu g,
      realWhittakerCharacter_padGL h hp]
    calc
      realWhittakerCharacter a u * W (padGL hp g) * (realWhittakerCharacter (-a) u * W' g) =
          (realWhittakerCharacter a u * realWhittakerCharacter (-a) u) *
            (W (padGL hp g) * W' g) := by
        ring
      _ = W (padGL hp g) * W' g := by rw [realWhittakerCharacter_mul_neg, one_mul]
  exact exists_convergence h D hW.2.1.continuous hW'.2.1.continuous hinv
    (RealWhittakerGauge.exists_gauge_bound hreg hgrowth)
    (RealWhittakerGauge.exists_gauge_bound hreg' hgrowth')

end Regular

end Langlands.Global.RankinSelbergGlobal.RealUnequalConvergence

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal

local instance realUneqStatementGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
local instance realUneqStatementGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
local instance realUneqStatementNMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
local instance realUneqStatementNBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
local instance realUneqStatementQMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.RankinSelberg.LeftUnipotentQuotient n ℝ) := borel _
local instance realUneqStatementQBorel (n : ℕ) :
    BorelSpace (Langlands.RankinSelberg.LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

/-- **Convergence and holomorphy of the real unequal-rank Rankin–Selberg integral**
(Jacquet 2009, Theorem 2.1(i), real case `n > m`, for the integral `Ψ(s; W, W')` and for
functions with uniformly bounded derivatives). Let `t < r`, let `W` on `GL_(r+1)(ℝ)` and `W'` on
`GL_(t+1)(ℝ)` be functions all of whose iterated right derivatives are smooth, transform on the
left under the upper unipotent group by the characters for `a` and `-a` respectively, and are
bounded by a constant times a fixed power (independent of the derivative) of the matrix height.
Then there is `σ` such that the integrand of `Ψ(s; W, W')` is integrable for the quotient
measure of `D` whenever `Re s > σ`, and `s ↦ Ψ(s; W, W')` is holomorphic on `Re s > σ`. -/
def RealUnequalConvergenceStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (D : RealQuotientMeasureData t) (a : ℝˣ)
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ),
    (∀ Xs, RealLocalWhittaker.iteratedRightDerivative r Xs W ∈
      RealLocalWhittaker.regularFunctions r a) →
    (∃ N : ℕ, ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖RealLocalWhittaker.iteratedRightDerivative r Xs W g‖ ≤ C * realMatrixHeight g ^ N) →
    (∀ Xs, RealLocalWhittaker.iteratedRightDerivative t Xs W' ∈
      RealLocalWhittaker.regularFunctions t (-a)) →
    (∃ N : ℕ, ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖RealLocalWhittaker.iteratedRightDerivative t Xs W' g‖ ≤ C * realMatrixHeight g ^ N) →
    ∃ σ : ℝ, (∀ s : ℂ, σ < s.re → Integrable (realUnequalIntegrand h W W' s) D.measure) ∧
      DifferentiableOn ℂ (realUnequalIntegral h D W W') {s : ℂ | σ < s.re}

theorem realUnequalConvergence : RealUnequalConvergenceStatement :=
  fun _ _ h D _ _ _ hreg hgrowth hreg' hgrowth' =>
    RealUnequalConvergence.exists_convergence_of_regular h D hreg hgrowth hreg' hgrowth'

end Langlands.Global.RankinSelbergGlobal
