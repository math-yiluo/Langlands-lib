import Langlands.Global.RankinSelberg.RealPairedStrictPrimal
import Langlands.Global.RankinSelberg.RealPairedWhittakerGauge

/-! # Initial convergence of ordinary integrals for genuine smooth real pairs -/

noncomputable section

open Matrix MeasureTheory
open Langlands.Archimedean Langlands.Archimedean.DerivativeSmoothVectors
open scoped ContDiff Manifold Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 1100000

namespace Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising

open ArchimedeanLocal CompletedProjectiveRepresentation RealPaddedExponential
open RealPairedSmoothRowAbsorption (slot unitProjection_slot_self unitProjection_slot_of_ne)
open RealPairedWhittakerGauge (coefficient realPairedWhittakerGauge)
open RealPaddedWhittakerProduct (oppositeScale)
open RealIwasawa (torus)
open RealConvergenceAnalysis (rootPos)
open RealUnequalConvergence (padVec padGL_torus padUnitary rootPos_padVec sum_abs_padVec)
open RealEqualConvergence (HasOrdinaryToralBound exists_convergence_of_toral_bound logDet
  exists_norm_le_exp hasRapidDecay_schwartz exp_le_mul_norm_lastRow)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable archimedeanRealQBorel

local notation "G" => fun r : ℕ => Langlands.GeneralLinear (r + 1) ℝ
local notation "Q" => fun r : ℕ => Langlands.RankinSelberg.LeftUnipotentQuotient r ℝ
local notation "N" => fun r : ℕ => Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "K" => fun r : ℕ => unitaryCompact ℝ (r + 1)
local notation "Mat" => fun r : ℕ => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "Row" => fun r : ℕ => Fin (r + 1) → ℝ
local notation "last" => Langlands.RankinSelberg.lastRow

private theorem padVec_self {r : ℕ} (y : Row r) : padVec r y = y :=
  funext (RealUnequalConvergence.extVec_fin y)

private theorem sum_abs_padVec_le {m r : ℕ} (hr : m ≤ r) (y : Row m) :
    ∑ j, |padVec r y j| = ∑ j, |y j| := by
  obtain h | rfl := lt_or_eq_of_le hr
  · exact sum_abs_padVec h y
  · rw [padVec_self]

private theorem rootPos_le_padVec {m r : ℕ} (hr : m ≤ r) (y : Row m) :
    rootPos y ≤ rootPos (padVec r y) := by
  obtain h | rfl := lt_or_eq_of_le hr
  · rw [rootPos_padVec h]
    exact le_add_of_nonneg_right (le_max_right _ _)
  · rw [padVec_self]

private theorem padGL_torus_mul {m r : ℕ} (h : m + 1 ≤ r + 1) (y : Row m) (b : K m) :
    padGL h (torus y * b.val) = torus (padVec r y) * (padUnitary h b).val := by
  rw [map_mul, padGL_torus]
  rfl

variable (n : Fin 2 → ℕ)

local notation "A" => fun i => Mat (n i)
local notation "B" => (∀ i : Fin 2, A i)
local notation "I" => 𝓘(ℝ, B)
local notation "pad" => fun m (hm : ∀ i, m ≤ n i) =>
  padProductGL (fun i => n i + 1) (fun i => Nat.succ_le_succ (hm i))

private theorem pad_eq_slots {m : ℕ} (hm : ∀ i, m ≤ n i) {i j : Fin 2} (hij : i ≠ j) (g : G m) :
    pad m hm g = slot n j (padGL (Nat.succ_le_succ (hm j)) g) *
      slot n i (padGL (Nat.succ_le_succ (hm i)) g) := by
  apply Units.ext
  funext l
  change (padGL (Nat.succ_le_succ (hm l)) g).val = (unitProjection A l
    (slot n j (padGL (Nat.succ_le_succ (hm j)) g) * slot n i (padGL (Nat.succ_le_succ (hm i)) g))).val
  rw [map_mul]
  have cases₂ : ∀ (i j l : Fin 2), i ≠ j → l = i ∨ l = j := by decide
  obtain rfl | rfl := cases₂ i j l hij
  · rw [unitProjection_slot_self, unitProjection_slot_of_ne n hij, one_mul]
  · rw [unitProjection_slot_self, unitProjection_slot_of_ne n hij.symm, mul_one]

variable (E : Fin 2 → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)] (R : ∀ i, G (n i) →* (E i →L[ℂ] E i))

local notation "P" => productAction A R
local notation "D" => DerivativeSmoothVectors I P
local notation "act" => DerivativeSmoothVectors.representation I P
local notation "Rows" => fun m => 𝓢(Row m, ℂ)
local notation "Terms" => fun m => D × Option (Rows m)

/-- The paired quotient integrals converge absolutely and are holomorphic on a common right
half-plane whenever a Schwartz row is supplied or one of the two paddings is strict. -/
def RealPairedOrdinaryConvergenceStatement : Prop :=
  (∀ i, IsContinuousRepresentation (R i)) →
  ∀ (a : ℝˣ) (T : D →L[ℂ] ℂ) (m : ℕ) (hm : ∀ i, m ≤ n i) (μ : RealQuotientMeasureData m),
    (∀ (i : Fin 2) (u : N (n i)) (v : D), T (act (slot n i u.val) v) =
      realWhittakerCharacter (oppositeScale a i) u.val * T v) →
    (∀ (u : N m) (v : D), T (act (pad m hm u.val) v) = T v) →
    ∃ σ : ℝ, ∀ v : Terms m, (v.2.isSome ∨ ∃ i, m < n i) →
      (∀ s : ℂ, σ < s.re → Integrable (ordinaryPaddedPairKernel n E R m hm T v s) μ.measure) ∧
      DifferentiableOn ℂ (ordinaryPaddedPairIntegral n E R m hm μ T v) {s | σ < s.re}

set_option maxHeartbeats 1500000 in
theorem realPairedOrdinaryConvergence : RealPairedOrdinaryConvergenceStatement n E R := by
  intro hR a T m hm μ hCov hInv
  obtain ⟨d, hG⟩ := realPairedWhittakerGauge n E R hR a T hCov
  let growth : ℝ := ((2 * d : ℕ) : ℝ) + ((2 * d : ℕ) : ℝ)
  have hGrowth : 0 ≤ growth := by positivity
  let shift : ℝ := (((n 0 - m : ℕ) : ℝ) + ((n 1 - m : ℕ) : ℝ)) / 2
  have hShift : (shift : ℂ) = pairedDetShift n m := by simp [shift, pairedDetShift]
  obtain ⟨σ, hConv⟩ := exists_convergence_of_toral_bound μ hGrowth shift
  let W (v : D) (g : G m) : ℂ := T (act (pad m hm g) v)
  have hW (v : D) : Continuous (W v) :=
    (contMDiff_smoothScalarCoefficient P T v).continuous.comp (continuous_padProductGL _ _)
  have hWInv (v : D) (u : N m) (g : G m) : W v (u.val * g) = W v g := by
    unfold W
    rw [map_mul, map_mul, Module.End.mul_apply, hInv]
  have hPadded (i : Fin 2) (v : D) (M : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : Row m) (b : K m),
        ‖W v (torus y * b.val)‖ ≤ C * Real.exp (-(M : ℝ) * rootPos (padVec (n i) y) +
          growth * ∑ l, |y l|) := by
    have hOther : ∀ i : Fin 2, i ≠ i + 1 := by decide
    let j : Fin 2 := i + 1
    have hij : i ≠ j := hOther i
    obtain ⟨C, hC, hb⟩ := hG i j hij v M
    let C' : ℝ := (2 * ((n j : ℝ) + 1) ^ 2) ^ d
    have hC' : 0 ≤ C' := by positivity
    refine ⟨C * C', mul_nonneg hC hC', fun y b => ?_⟩
    have e : W v (torus y * b.val) = coefficient n E R T i j
        (padGL (Nat.succ_le_succ (hm j)) (torus y * b.val)) v
        (torus (padVec (n i) y) * (padUnitary (Nat.succ_le_succ (hm i)) b).val) := by
      unfold W coefficient
      rw [pad_eq_slots n hm hij, padGL_torus_mul (Nat.succ_le_succ (hm i))]
    have hHeight := RealWhittakerGauge.realMatrixHeight_torus_mul_pow_le (padVec (n j) y)
      (padUnitary (Nat.succ_le_succ (hm j)) b) d
    rw [sum_abs_padVec_le (hm j), ← padGL_torus_mul (Nat.succ_le_succ (hm j))] at hHeight
    rw [e]
    refine ((hb (padVec (n i) y) (padUnitary (Nat.succ_le_succ (hm i)) b) _).trans
      (mul_le_mul_of_nonneg_left hHeight (by positivity))).trans_eq ?_
    rw [sum_abs_padVec_le (hm i)]
    change (C * Real.exp (-(M : ℝ) * rootPos (padVec (n i) y) + ↑(2 * d) * ∑ l, |y l|)) *
      (C' * Real.exp (↑(2 * d) * ∑ l, |y l|)) = _
    rw [show ∀ x y : ℝ, (C * x) * (C' * y) = C * C' * (x * y) by intros; ring, ← Real.exp_add]
    congr 2
    dsimp [growth]
    ring
  refine ⟨σ, fun v hv => ?_⟩
  let F (g : G m) : ℂ := W v.1 g * v.2.elim 1 (fun φ => φ (last g))
  have hRow : Continuous (last : G m → Row m) :=
    continuous_pi fun l => (Langlands.GeneralLinear.entry (Fin.last m) l).continuous
  have hF : Continuous F := by
    cases he : v.2 with
    | none => simpa only [F, he, Option.elim_none, mul_one] using hW v.1
    | some φ =>
      simp only [F, he, Option.elim_some]
      exact (hW v.1).mul (φ.continuous.comp hRow)
  have hFInv (u : N m) (g : G m) : F (u.val * g) = F g := by
    simp only [F, hWInv, Langlands.RankinSelberg.lastRow_unipotent_mul]
  have hBound : HasOrdinaryToralBound growth F := by
    intro M
    cases he : v.2 with
    | none =>
      have hlt : ∃ i, m < n i := by simpa [he] using hv
      obtain ⟨i, hi⟩ := hlt
      obtain ⟨C, hC, hb⟩ := hPadded i v.1 M
      refine ⟨C, hC, fun y b => ?_⟩
      simp only [F, he, Option.elim_none, mul_one]
      refine (hb y b).trans_eq ?_
      rw [rootPos_padVec hi]
      congr 2
      ring
    | some φ =>
      obtain ⟨C, hC, hb⟩ := hPadded 0 v.1 M
      obtain ⟨C', hC', hφ⟩ := exists_norm_le_exp (hasRapidDecay_schwartz φ)
        (c := (m : ℝ) + 1) (by positivity) M
      refine ⟨C * C', mul_nonneg hC hC', fun y b => ?_⟩
      simp only [F, he, Option.elim_some, norm_mul]
      have hRowBound := hφ _ (y (Fin.last m)) (exp_le_mul_norm_lastRow y b)
      refine (mul_le_mul (hb y b) hRowBound (norm_nonneg _) (by positivity)).trans ?_
      rw [show ∀ x y : ℝ, (C * x) * (C' * y) = C * C' * (x * y) by intros; ring, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (mul_nonneg hC hC')
      have hRoot := mul_le_mul_of_nonpos_left (rootPos_le_padVec (hm 0) y)
        (neg_nonpos.mpr (Nat.cast_nonneg (α := ℝ) M))
      linarith
  have hConv' := hConv F hF hFInv hBound
  have he (s : ℂ) : ordinaryPaddedPairKernel n E R m hm T v s = fun q =>
      F q.out * Complex.exp ((s - pairedDetShift n m) * (logDet q.out : ℂ)) := rfl
  simp only [hShift, ← he] at hConv'
  exact hConv'

end Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising
