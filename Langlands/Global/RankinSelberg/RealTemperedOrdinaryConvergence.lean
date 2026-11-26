import Langlands.Global.RankinSelberg.RealToralQuotientDensity
import Langlands.Global.RankinSelberg.RealUnequalPairConvergence

/-! # Sharp ordinary real convergence from tempered Whittaker bounds -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker

open Langlands.Archimedean (unitaryCompact)
open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow)
open Langlands.QuotientIntegration (descend)
open ArchimedeanLocal RealIwasawa RealConvergenceAnalysis
open RealLocalWhittaker (regularFunctions iteratedRightDerivative)
open RealEqualConvergence RealEqualDualConvergence

local instance (m : ℕ) : MeasurableSpace (Langlands.GeneralLinear (m + 1) ℝ) := borel _
local instance (m : ℕ) : BorelSpace (Langlands.GeneralLinear (m + 1) ℝ) := ⟨rfl⟩
local instance (m : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent (m + 1) ℝ) := borel _
local instance (m : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent (m + 1) ℝ) := ⟨rfl⟩
local instance (m : ℕ) : MeasurableSpace (LeftUnipotentQuotient m ℝ) := borel _
local instance (m : ℕ) : BorelSpace (LeftUnipotentQuotient m ℝ) := ⟨rfl⟩

variable {r t : ℕ}
local notation "G" => fun r => Langlands.GeneralLinear (r + 1) ℝ

/-- The modulus to the power one half, with an arbitrarily small exponential error
in the logarithmic diagonal. The condition applies to all right-derivative words. -/
def HasTemperedDerivativeBound (W : G r → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ Xs, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (y : Fin (r + 1) → ℝ) (k : unitaryCompact ℝ (r + 1)),
      ‖iteratedRightDerivative r Xs W (torus y * k.val)‖ ≤
        C * Real.exp (torusModularLog (r + 1) y / 2 + ε * ∑ j, |y j|)

/-- The tempered modulus bound with arbitrary rapid decay in positive simple roots. -/
def HasTemperedGauge (W : G r → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (y : Fin (r + 1) → ℝ) (k : unitaryCompact ℝ (r + 1)),
      ‖W (torus y * k.val)‖ ≤
        C * Real.exp (torusModularLog (r + 1) y / 2 + ε * ∑ j, |y j| - (M : ℝ) * rootPos y)

theorem hasTemperedGauge_of_derivativeBound {a : ℝˣ} {W : G r → ℂ}
    (hreg : ∀ Xs, iteratedRightDerivative r Xs W ∈ regularFunctions r a)
    (hW : HasTemperedDerivativeBound W) : HasTemperedGauge W := by
  classical
  intro ε hε M
  let weight (g : G r) := Real.exp (torusModularLog (r + 1) (alpha g) / 2 +
    ε * ∑ j, |alpha g j|)
  have hweight (g : G r) : 0 ≤ weight g := (Real.exp_pos _).le
  have hbase (Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (_ : Unit) (g : G r),
        ‖iteratedRightDerivative r Xs W g‖ ≤ C * weight g := by
    obtain ⟨C, hC, hb⟩ := hW ε hε Xs
    refine ⟨C, hC, fun _ g => ?_⟩
    conv_lhs => rw [← npart_mul_torus_mul_kpart g, mul_assoc, (hreg Xs).1 _ (npart g).2,
      norm_mul, RealUnequalPairConvergence.norm_realWhittakerCharacter, one_mul]
    exact hb (alpha g) (kpart g)
  have hS : ∀ S : Finset (Fin r), ∃ C : ℝ, 0 ≤ C ∧ ∀ g : G r,
      ‖W g‖ ≤ C * (∏ i : Fin r, RealWhittakerGauge.rootSize g i ^
        (if i ∈ S then M else 0)) * weight g := by
    intro S
    obtain ⟨is, his⟩ := RealWhittakerGauge.exists_list_prod (fun i : Fin r => if i ∈ S then M else 0)
    obtain ⟨C, hC, hb⟩ := RealWhittakerGauge.exists_weighted_bound_list_family
      (fun _ : Unit => W) (fun _ => hreg) hweight hbase is []
    refine ⟨C, hC, fun g => ?_⟩
    simpa only [his, iteratedRightDerivative, List.foldr_nil] using hb () g
  choose C hC hb using hS
  let P : ℝ := ((((r : ℝ) + 1) ^ 2) ^ M) ^ r
  have hC0 : 0 ≤ ∑ S, C S := Finset.sum_nonneg fun S _ => hC S
  refine ⟨(∑ S, C S) * P, by positivity, fun y k => ?_⟩
  let S := Finset.univ.filter (fun i : Fin r => 0 ≤ y i.castSucc - y i.succ)
  have hCS : C S ≤ ∑ S, C S := Finset.single_le_sum (fun S _ => hC S) (Finset.mem_univ S)
  have hP := RealWhittakerGauge.prod_rootSize_pow_le y k M
  have hα : alpha (torus y * k.val) = y := by
    simpa using alpha_iwasawa (1 : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ) y k
  calc
    _ ≤ C S * (∏ i : Fin r, RealWhittakerGauge.rootSize (torus y * k.val) i ^
        (if i ∈ S then M else 0)) * weight (torus y * k.val) := hb S _
    _ ≤ ((∑ S, C S) * (P * Real.exp (-(M : ℝ) * rootPos y))) * weight (torus y * k.val) := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul hCS hP ?_ hC0) (hweight _)
      exact Finset.prod_nonneg fun i _ => pow_nonneg (RealWhittakerGauge.rootSize_nonneg _ _) _
    _ = _ := by
      dsimp only [weight]
      rw [hα]
      let T := torusModularLog (r + 1) y / 2 + ε * ∑ j, |y j|
      change _ * Real.exp T = _ * Real.exp (T - (M : ℝ) * rootPos y)
      have hexp : Real.exp (T - (M : ℝ) * rootPos y) =
          Real.exp T * Real.exp (-(M : ℝ) * rootPos y) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      ring

theorem torusModularLog_revNeg (y : Fin (r + 1) → ℝ) :
    torusModularLog (r + 1) (revNeg y) = torusModularLog (r + 1) y := by
  simp only [torusModularLog_apply, revNeg, Nat.cast_succ, add_sub_cancel_right]
  rw [← Equiv.sum_comp Fin.revPerm (fun j : Fin (r + 1) => ((r : ℝ) - 2 * j.val) * y j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have he : j.rev.val = r - j.val := by rw [Fin.val_rev]; omega
  rw [Fin.revPerm_apply, he, Nat.cast_sub (Nat.le_of_lt_succ j.isLt)]
  ring

theorem HasTemperedGauge.dual {W : G r → ℂ} (hW : HasTemperedGauge W) :
    HasTemperedGauge (ArchimedeanLocal.dualFunction (r + 1) W) := by
  intro ε hε M
  obtain ⟨C, hC, hb⟩ := hW ε hε M
  refine ⟨C, hC, fun y k => ?_⟩
  rw [dual_torus_mul]
  simpa only [torusModularLog_revNeg, rootPos_revNeg, sum_abs_revNeg] using
    hb (revNeg y) (weylUnitary k)

theorem torusModularLog_padVec (h : t < r) (y : Fin (t + 1) → ℝ) :
    torusModularLog (r + 1) (RealUnequalConvergence.padVec r y) =
      torusModularLog (t + 1) y + ((r : ℝ) - t) * ∑ j, y j := by
  open RealUnequalConvergence in
  let f (j : ℕ) := ((r : ℝ) - 2 * j) * extVec y j
  rw [torusModularLog_apply, torusModularLog_apply]
  simp only [Nat.cast_succ, add_sub_cancel_right]
  change ∑ j : Fin (r + 1), f j.val = _
  rw [Fin.sum_univ_eq_sum_range, ← Finset.sum_range_add_sum_Ico f (Nat.succ_le_succ h.le),
    ← Fin.sum_univ_eq_sum_range f (t + 1)]
  have hzero : ∑ j ∈ Finset.Ico (t + 1) (r + 1), f j = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    simp [f, RealUnequalConvergence.extVec_of_le y (Finset.mem_Ico.mp hj).1]
  rw [hzero, add_zero, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [f, RealUnequalConvergence.extVec_fin]
  ring

private theorem exponent_le_with_decay (y : Fin (r + 1) → ℝ) {τ c M : ℝ} (hc : 0 < c)
    (hτ : 2 * c * ((r : ℝ) + 1) ≤ τ)
    (hM : 2 * c * ((r : ℝ) + 1) + τ * ((r : ℝ) + 1) ≤ M) :
    -M * (rootPos y + max (y (Fin.last r)) 0) + c * (∑ j, |y j|) +
      τ * (∑ j, y j) ≤ -c * ∑ j, |y j| := by
  set n : ℝ := (r : ℝ) + 1
  have ht : (1 + 1) * n ≤ τ / c := by
    apply (le_div_iff₀ hc).2
    linarith only [hτ, show (1 + 1) * n * c = 2 * c * n by ring]
  have hM' : (1 + 1) * n + (τ / c) * n ≤ M / c := by
    apply (le_div_iff₀ hc).2
    calc
      _ = 2 * c * n + ((τ / c) * c) * n := by ring
      _ ≤ _ := by rwa [div_mul_cancel₀ _ hc.ne']
  have hb := exponent_le y (A := 1) (t := τ / c) (M := M / c) (K := M / c) zero_le_one ht hM' hM'
  have hmul := mul_le_mul_of_nonneg_right hb hc.le
  convert hmul using 1
  · field_simp
    ring
  · field_simp

/-- Holomorphy and absolute convergence for a left-unipotent invariant kernel whose
toral bound has the full modulus and arbitrarily small residual growth. -/
theorem positiveHalfPlane_of_toral_bound (D : RealQuotientMeasureData r) {K : G r → ℂ}
    (hK : Continuous K)
    (hinv : ∀ u : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g, K (u.val * g) = K g)
    (hb : ∀ ε : ℝ, 0 < ε → ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (y : Fin (r + 1) → ℝ) (k : unitaryCompact ℝ (r + 1)),
        ‖K (torus y * k.val)‖ ≤ C * Real.exp (torusModularLog (r + 1) y +
          ε * ∑ j, |y j| - (M : ℝ) * (rootPos y + max (y (Fin.last r)) 0))) :
    (∀ s : ℂ, 0 < s.re → Integrable
      (fun q => K q.out * Complex.exp (s * (logDet q.out : ℂ))) D.measure) ∧
    DifferentiableOn ℂ (fun s => ∫ q, K q.out * Complex.exp (s * (logDet q.out : ℂ)) ∂D.measure)
      {s : ℂ | 0 < s.re} := by
  have := D.groupHaar_isHaar
  have := D.unipotentHaar_isHaar
  have := D.unipotentHaar_rightInvariant
  obtain ⟨κ, hκ⟩ := realToralQuotientDensity D.groupHaar D.unipotentHaar D.measure D.compatible
  let f (q : LeftUnipotentQuotient r ℝ) := K q.out
  let ℓ (q : LeftUnipotentQuotient r ℝ) := logDet q.out
  have hlinv (u : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ) (g : G r) :
      logDet (u.val * g) = logDet g := logDet_unipotent_mul u g
  have hfc : Continuous f :=
    (continuous_descend hinv hK).congr (fun q => (out_eq_descend K hinv q).symm)
  have hℓc : Continuous ℓ :=
    (continuous_descend_real hlinv continuous_logDet).congr
      (fun q => (out_eq_descend logDet hlinv q).symm)
  have hℓ (q : LeftUnipotentQuotient r ℝ) : ℓ q = ∑ j, alphaQ q j := by
    rw [← alpha_out q, ← logDet_torus_mul (alpha q.out) (kpart q.out)]
    exact eq_torus_mul_kpart logDet hlinv q.out
  have hint (τ : ℝ) (hτ : 0 < τ) :
      Integrable (fun q => ‖f q‖ * Real.exp (τ * ℓ q)) D.measure := by
    let c : ℝ := τ / (2 * ((r : ℝ) + 1))
    let M : ℕ := ⌈2 * c * ((r : ℝ) + 1) + τ * ((r : ℝ) + 1)⌉₊
    have hc : 0 < c := by dsimp [c]; positivity
    have hτ' : 2 * c * ((r : ℝ) + 1) ≤ τ := by
      have hn : 0 < (r : ℝ) + 1 := by positivity
      suffices 2 * c * ((r : ℝ) + 1) = τ by linarith
      dsimp only [c]
      field_simp
    obtain ⟨C, hC, hB⟩ := hb c hc M
    let E (y : Fin (r + 1) → ℝ) := torusModularLog (r + 1) y +
      c * ∑ j, |y j| - (M : ℝ) * (rootPos y + max (y (Fin.last r)) 0) + τ * ∑ j, y j
    have hE : Continuous E := by
      exact ((((torusModularLog (r + 1)).continuous.add
        (continuous_const.mul (continuous_finsetSum _ fun j _ => (continuous_apply j).abs))).sub
        (continuous_const.mul (continuous_rootPos.add ((continuous_apply _).max continuous_const)))).add
        (continuous_const.mul (continuous_finsetSum _ fun j _ => continuous_apply j)))
    have hEL (y : Fin (r + 1) → ℝ) : (-torusModularLog (r + 1)) y + E y ≤
        -c * ∑ j, |y j| := by
      have hb' := exponent_le_with_decay y hc hτ' (Nat.le_ceil (2 * c * ((r : ℝ) + 1) + τ * ((r : ℝ) + 1)))
      convert hb' using 1
      simp only [E, neg_apply]
      ring
    have hI := (RealUnequalDualConvergence.integrable_exp_comp_alphaQ_of_le
      (L := -torusModularLog (r + 1)) hκ hE hc hEL).const_mul C
    refine hI.mono' ((hfc.norm.mul (Real.continuous_exp.comp
      (continuous_const.mul hℓc))).aestronglyMeasurable) (ae_of_all _ fun q => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le), hℓ q]
    have hfq : f q = K (torus (alphaQ q) * (kpart q.out).val) := by
      rw [← alpha_out q]
      exact eq_torus_mul_kpart K hinv q.out
    rw [hfq]
    dsimp only [E]
    rw [Real.exp_add, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hB _ _) (Real.exp_pos _).le
  refine ⟨fun s hs => ?_, differentiableOn_integral_cexp_mul
    hfc.aestronglyMeasurable hℓc.aestronglyMeasurable hint⟩
  refine (hint s.re hs).mono' ((hfc.mul (Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp hℓc)))).aestronglyMeasurable)
      (ae_of_all _ fun q => ?_)
  rw [norm_mul, norm_cexp_mul_ofReal]

theorem equal_positiveHalfPlane (D : RealQuotientMeasureData r) {W V : G r → ℂ}
    {Φ : (Fin (r + 1) → ℝ) → ℂ} (hWc : Continuous W) (hVc : Continuous V)
    (hΦc : Continuous Φ) (hΦ : HasRapidDecay Φ)
    (hinv : ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
      W (u * g) * V (u * g) = W g * V g)
    (hW : HasTemperedGauge W) (hV : HasTemperedGauge V) :
    (∀ s : ℂ, 0 < s.re → Integrable (realEqualIntegrand W V Φ s) D.measure) ∧
    DifferentiableOn ℂ (realEqualIntegral D W V Φ) {s : ℂ | 0 < s.re} := by
  refine positiveHalfPlane_of_toral_bound D (K := kernel W V Φ) (continuous_kernel hWc hVc hΦc)
    (fun u g => kernel_unipotent_mul hinv u g) ?_
  intro ε hε M
  obtain ⟨C₁, hC₁, h₁⟩ := hW (ε / 2) (by positivity) M
  obtain ⟨C₂, hC₂, h₂⟩ := hV (ε / 2) (by positivity) 0
  obtain ⟨C₃, hC₃, h₃⟩ := exists_norm_le_exp hΦ (c := (r : ℝ) + 1) (by positivity) M
  refine ⟨C₁ * C₂ * C₃, by positivity, fun y k => ?_⟩
  let A := torusModularLog (r + 1) y / 2 + ε / 2 * ∑ j, |y j|
  let B := -(M : ℝ) * rootPos y
  let C := -(M : ℝ) * max (y (Fin.last r)) 0
  have hW' : ‖W (torus y * k.val)‖ ≤ C₁ * Real.exp (A + B) := by
    simpa only [A, B, sub_eq_add_neg, neg_mul] using h₁ y k
  have hV' : ‖V (torus y * k.val)‖ ≤ C₂ * Real.exp A := by simpa [A] using h₂ y k
  have hΦ' : ‖Φ (lastRow (torus y * k.val))‖ ≤ C₃ * Real.exp C :=
    h₃ _ _ (exp_le_mul_norm_lastRow y k)
  calc
    _ ≤ (C₁ * Real.exp (A + B)) * (C₂ * Real.exp A) * (C₃ * Real.exp C) := by
      unfold kernel
      rw [norm_mul, norm_mul]
      gcongr
    _ = C₁ * C₂ * C₃ * (Real.exp (A + B) * Real.exp A * Real.exp C) := by ring
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      dsimp only [A, B, C]
      ring

theorem unequal_positiveHalfPlane (h : t < r) (D : RealQuotientMeasureData t)
    {W : G r → ℂ} {V : G t → ℂ} (hWc : Continuous W) (hVc : Continuous V)
    (hinv : ∀ u ∈ Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ, ∀ g,
      RealUnequalConvergence.kernel (Nat.le_of_lt (Nat.succ_lt_succ h)) W V (u * g) =
        RealUnequalConvergence.kernel (Nat.le_of_lt (Nat.succ_lt_succ h)) W V g)
    (hW : HasTemperedGauge W) (hV : HasTemperedGauge V) :
    (∀ s : ℂ, 0 < s.re → Integrable (realUnequalIntegrand h W V s) D.measure) ∧
    DifferentiableOn ℂ (realUnequalIntegral h D W V) {s : ℂ | 0 < s.re} := by
  let hp := Nat.le_of_lt (Nat.succ_lt_succ h)
  let c : ℝ := ((r - t : ℕ) : ℝ) / 2
  let K (g : G t) := RealUnequalConvergence.kernel hp W V g * Complex.exp (-(c : ℂ) * (logDet g : ℂ))
  have hK : Continuous K := (RealUnequalConvergence.continuous_kernel hp hWc hVc).mul
    (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp continuous_logDet)))
  have hKinv (u : Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ) (g : G t) :
      K (u.val * g) = K g := by
    dsimp only [K]
    rw [hinv _ u.2 g, logDet_unipotent_mul]
  have heq (s : ℂ) : realUnequalIntegrand h W V s =
      fun q => K q.out * Complex.exp (s * (logDet q.out : ℂ)) := by
    funext q
    change W (padGL hp q.out) * V q.out *
        Complex.exp ((s - ((r - t : ℕ) : ℂ) / 2) * (logDet q.out : ℂ)) =
      K q.out * Complex.exp (s * (logDet q.out : ℂ))
    dsimp only [K, RealUnequalConvergence.kernel, c]
    rw [mul_assoc (W (padGL hp q.out) * V q.out), ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hPos := positiveHalfPlane_of_toral_bound D hK hKinv (by
    intro ε hε M
    obtain ⟨C₁, hC₁, h₁⟩ := hW (ε / 2) (by positivity) M
    obtain ⟨C₂, hC₂, h₂⟩ := hV (ε / 2) (by positivity) 0
    refine ⟨C₁ * C₂, by positivity, fun y k => ?_⟩
    have hPad : padGL hp (torus y * k.val) =
        torus (RealUnequalConvergence.padVec r y) * (RealUnequalConvergence.padUnitary hp k).val := by
      rw [map_mul, RealUnequalConvergence.padGL_torus]
      rfl
    let A := torusModularLog (t + 1) y / 2 + ε / 2 * ∑ j, |y j|
    let B := -(M : ℝ) * (rootPos y + max (y (Fin.last t)) 0)
    let T := c * ∑ j, y j
    have hW' : ‖W (padGL hp (torus y * k.val))‖ ≤ C₁ * Real.exp (A + T + B) := by
      rw [hPad]
      refine (h₁ _ _).trans_eq ?_
      rw [torusModularLog_padVec h, RealUnequalConvergence.sum_abs_padVec h,
        RealUnequalConvergence.rootPos_padVec h]
      congr 2
      simp only [A, B, T, c, Nat.cast_sub h.le]
      ring
    have hV' : ‖V (torus y * k.val)‖ ≤ C₂ * Real.exp A := by simpa [A] using h₂ y k
    have hnorm : ‖Complex.exp (-(c : ℂ) * (logDet (torus y * k.val) : ℂ))‖ =
        Real.exp (-T) := by
      rw [logDet_torus_mul, norm_cexp_mul_ofReal]
      simp [T, neg_mul]
    calc
      _ ≤ (C₁ * Real.exp (A + T + B)) * (C₂ * Real.exp A) * Real.exp (-T) := by
        dsimp only [K, RealUnequalConvergence.kernel]
        rw [norm_mul, norm_mul, hnorm]
        gcongr
      _ = C₁ * C₂ * (Real.exp (A + T + B) * Real.exp A * Real.exp (-T)) := by ring
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        dsimp only [A, B]
        ring)
  exact ⟨fun s hs => heq s ▸ hPos.1 s hs, by
    have hfun : realUnequalIntegral h D W V =
        fun s => ∫ q, K q.out * Complex.exp (s * (logDet q.out : ℂ)) ∂D.measure := by
      funext s
      change (∫ q, realUnequalIntegrand h W V s q ∂D.measure) = _
      rw [heq]
    rw [hfun]
    exact hPos.2⟩

/-- The tempered toral gauge gives convergence and holomorphy on the positive half-plane
for the ordinary integrals, including the Fourier-reflected equal-rank integral. -/
def RealTemperedOrdinaryConvergenceStatement : Prop :=
  (∀ (r t : ℕ) (h : t < r) (D : RealQuotientMeasureData t) (a : ℝˣ)
    (W : G r → ℂ) (V : G t → ℂ), W ∈ regularFunctions r a → V ∈ regularFunctions t (-a) →
    HasTemperedGauge W → HasTemperedGauge V →
    (∀ s : ℂ, 0 < s.re → Integrable (realUnequalIntegrand h W V s) D.measure) ∧
    DifferentiableOn ℂ (realUnequalIntegral h D W V) {s : ℂ | 0 < s.re}) ∧
  (∀ (r : ℕ) (D : RealQuotientMeasureData r) (a b : ℝˣ)
    (W V : G r → ℂ) (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ),
    W ∈ regularFunctions r a → V ∈ regularFunctions r (-a) →
    HasTemperedGauge W → HasTemperedGauge V →
    (∀ s : ℂ, 0 < s.re → Integrable (realEqualIntegrand W V Φ s) D.measure ∧
      Integrable (realEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
        (ArchimedeanLocal.dualFunction (r + 1) V) (realFourierTransform b Φ) s) D.measure) ∧
    DifferentiableOn ℂ (realEqualIntegral D W V Φ) {s : ℂ | 0 < s.re} ∧
    DifferentiableOn ℂ (realEqualDualIntegral b D W V Φ) {s : ℂ | 0 < s.re})

theorem realTemperedOrdinaryConvergence : RealTemperedOrdinaryConvergenceStatement := by
  constructor
  · intro r t h D a W V hW hV hWg hVg
    refine unequal_positiveHalfPlane h D hW.2.1.continuous hV.2.1.continuous ?_ hWg hVg
    intro u hu g
    unfold RealUnequalConvergence.kernel
    rw [map_mul, hW.1 _ (RealUnequalConvergence.padGL_mem_upperUnipotent _ hu), hV.1 u hu g,
      RealUnequalConvergence.realWhittakerCharacter_padGL h]
    rw [mul_mul_mul_comm, realWhittakerCharacter_mul_neg, one_mul]
  · intro r D a b W V Φ hW hV hWg hVg
    have hinv (u) (hu : u ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ) (g : G r) :
        W (u * g) * V (u * g) = W g * V g := by
      rw [hW.1 u hu g, hV.1 u hu g, mul_mul_mul_comm, realWhittakerCharacter_mul_neg, one_mul]
    have hp := equal_positiveHalfPlane D hW.2.1.continuous hV.2.1.continuous Φ.continuous
      (hasRapidDecay_schwartz Φ) hinv hWg hVg
    obtain ⟨hΦc, hΦ⟩ := fourier_rapidDecay b Φ
    have hd := equal_positiveHalfPlane D (continuous_dual hW.2.1.continuous)
      (continuous_dual hV.2.1.continuous) hΦc hΦ (dual_mul_invariant hinv) hWg.dual hVg.dual
    exact ⟨fun s hs => ⟨hp.1 s hs, hd.1 s hs⟩, hp.2, hd.2⟩

end Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker
