import Langlands.Global.RankinSelberg.ComplexGapAlternateHeight
import Langlands.Global.RankinSelberg.ComplexGapAlternateTailConvergence

/-! # Pointwise bounds for the complex alternate chart kernel -/

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapAlternateMajorant

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal (complexNormalizedAbs)
open ComplexGapAlternateHeight (complexGapAlternateHeight)
open ComplexGapInverseTransposeTailBound (inverseTailColumns)
open ComplexGapAlternateTailConvergence (alternateTailEnvelope)
open ComplexGapLeadingSchwartz (matrixDecay weightedMatrixTail exists_integrable_weightedMatrixTail)
open ComplexGapOrdinaryMajorant (leadingInput exists_leading_bound normalizedDet_eq_exp)
open ComplexGapTailEndpoints (firstTailColumn)
open ComplexLocalIwasawa (alpha alphaQ alphaQ_mk alpha_iwasawa logTorus_neg)
open ComplexLocalWhittakerGauge (logTorus)
open ComplexPlaceAnalytic (two_le_complexMatrixHeight)
open ComplexTwoBlockHaar (rightTail blockLog complexTwoBlockIwasawa)
open ComplexWhittakerTranslateBound (complexWhittakerTranslateBound)
open ComplexWhittakerTranslatedMellin (compact_rightTranslate_uniformSimpleRootBound)
open RealConvergenceAnalysis (rootPos)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "KU" => fun n => unitaryCompact ℂ n
local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℂ
local notation "H" => complexMatrixHeight
local notation "δ" => fun g => complexNormalizedAbs (Matrix.det (Units.val g))
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ
local notation "Tail" => fun r t => Q t × ((Fin (r + 1 - (t + 1)) → ℝ) ×
  (N (r + 1 - (t + 1)) × ((Fin (t + 1) → ℂ) × KU (r + 1))))

private def firstRectangle {r t : ℕ} (x : Fin (t + 1) → ℂ) : Mat (t + 1) (r + 1 - (t + 1)) :=
  fun i j => if j.val = 0 then x i else 0

private theorem sum_abs_blockLog {n k : ℕ} (hkn : k < n) (y : Fin k → ℝ)
    (z : Fin (n - k) → ℝ) :
    (∑ i, |blockLog hkn y z i|) = (∑ i, |y i|) + ∑ i, |z i| := by
  have h := Fintype.sum_equiv (finCongr (Nat.add_sub_of_le hkn.le)).symm
    (fun i => |blockLog hkn y z i|) (fun i => |Fin.append y z i|) (fun _ => rfl)
  rw [h, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- The pointwise norm product for the alternate block kernel. Each pullback preserves
or lowers matrix height. The scalar exponential can bound the remaining tail radial weights. -/
def alternateGapNorm {r t : ℕ} (h : t < r) (Φ : 𝓢(Mat (r + 1) (t + 1), ℂ))
    (φ : 𝓢(Fin (r + 1) → ℂ, ℂ)) (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ))
    (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ) (L : G (r + 1) → G (r + 1))
    (R : G (t + 1) → G (t + 1)) (u s b : ℝ)
    (p : Tail r t) (g₁ : G (t + 1)) (Y : Mat (r + 1 - (t + 1)) (t + 1)) : ℝ :=
  let hkn := Nat.succ_lt_succ h
  let hk := Nat.succ_pos t
  let z := p.2.1
  let B := rightTail hk hkn (logTorus (-z) * p.2.2.1.val)
    (firstRectangle (r := r) p.2.2.2.1) p.2.2.2.2
  let g := p.1.out
  ‖Φ ((L B).val * leadingInput (Nat.add_sub_of_le hkn.le) g₁.val Y)‖ *
    ‖φ (firstTailColumn hk hkn B) * Ξ (inverseTailColumns hkn B)‖ *
    ‖W (padGL hkn.le g * B⁻¹)‖ * ‖V (g * R g₁)‖ * δ g ^ u * δ g₁ ^ s *
    Real.exp (b * ∑ i, |z i|)

/-- The leading matrix and rectangle separate from the alternate tail envelope. -/
def ComplexGapAlternateMajorantStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (ds es : List ComplexCharacterData) (a : ℂˣ)
    (W : complexWhittakerModel r ds a) (V : complexWhittakerModel t es (-a))
    (L : G (r + 1) → G (r + 1)) (R : G (t + 1) → G (t + 1)),
    (∀ x, H (L x) ≤ H x) → (∀ x, H (R x) ≤ H x) →
    ∃ (τ A : ℝ) (M : ℕ), 0 ≤ A ∧
    ∀ (u s b : ℝ), τ ≤ s → 0 ≤ b →
    ∀ (Φ : 𝓢(Mat (r + 1) (t + 1), ℂ)) (φ : 𝓢(Fin (r + 1) → ℂ, ℂ))
      (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ)) (l : ℕ),
      ∃ (j m : ℕ) (B : ℝ), 0 ≤ B ∧ Integrable (weightedMatrixTail M j s) (complexGeneralLinearHaar (t + 1)) ∧
      ∀ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Tail r t) (g₁ : G (t + 1)) (Y : Mat (r + 1 - (t + 1)) (t + 1)),
        alternateGapNorm h Φ φ Ξ W.val V.val L R u s b p g₁ Y ≤
          C * weightedMatrixTail M j s g₁ * matrixDecay l Y *
            alternateTailEnvelope h φ Ξ A B (2 * u) J m m p

set_option maxHeartbeats 1250000 in
theorem complexGapAlternateMajorant : ComplexGapAlternateMajorantStatement := by
  intro r t h ds es a W V L R hL hR
  let n := r + 1
  let k := t + 1
  let d := n - k
  let hk : 0 < k := Nat.succ_pos t
  let hkn : k < n := Nat.succ_lt_succ h
  obtain ⟨N₁, hW⟩ := compact_rightTranslate_uniformSimpleRootBound W {1} isCompact_singleton
  obtain ⟨N₂, hV⟩ := complexWhittakerTranslateBound t es (-a) V
  obtain ⟨C₂, hC₂, hV₀⟩ := hV 0
  obtain ⟨C₃, m₀, hC₃, hChart⟩ := complexGapAlternateHeight r k hk hkn
  let M := N₂ * k
  let A : ℝ := N₁ + N₂
  refine ⟨(k : ℝ) + M, A, M, by dsimp only [A]; positivity, fun u s b hs hb Φ φ Ξ l => ?_⟩
  obtain ⟨j, hj⟩ := exists_integrable_weightedMatrixTail t M s hs
  obtain ⟨C₀, hC₀, hΦ⟩ := exists_leading_bound (Nat.add_sub_of_le hkn.le) (Nat.succ_pos r) Φ j l
  let m := m₀ * (j + l)
  let B : ℝ := N₁ + 2 * (j + l : ℕ) + b
  refine ⟨j, m, B, by dsimp only [B]; positivity, hj, fun J => ?_⟩
  obtain ⟨C₁, hC₁, hWJ⟩ := hW J
  refine ⟨C₀ * C₁ * C₂ * C₃ ^ (j + l), by positivity, fun p g₁ Y => ?_⟩
  let z := p.2.1
  let u₂ := p.2.2.1
  let X := firstRectangle (r := r) p.2.2.2.1
  let h₂ := logTorus (-z) * u₂.val
  let g₂ := rightTail hk hkn h₂ X p.2.2.2.2
  let g := p.1.out
  let y := alphaQ p.1
  let sy := ∑ i, |y i|
  let sz := ∑ i, |z i|
  let U := 1 + ‖firstTailColumn hk hkn g₂‖
  let Z := 1 + ‖inverseTailColumns hkn g₂‖
  let D := ‖φ (firstTailColumn hk hkn g₂) * Ξ (inverseTailColumns hkn g₂)‖
  have hy : alpha g = y := by
    dsimp only [g, y]
    conv_rhs => rw [← Quotient.out_eq p.1]
    exact (alphaQ_mk _).symm
  have hz : alpha h₂⁻¹ = z := by
    dsimp only [h₂]
    rw [mul_inv_rev, logTorus_neg, inv_inv]
    change alpha (u₂⁻¹.val * logTorus z) = z
    simpa only [OneMemClass.coe_one, mul_one] using alpha_iwasawa u₂⁻¹ z (1 : KU d)
  have hδ : δ g ^ u = Real.exp (2 * u * (∑ i, y i)) := by
    rw [normalizedDet_eq_exp, hy, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  have hchart := hChart z u₂ p.2.2.2.1 p.2.2.2.2
  change H g₂ ≤ C₃ * U ^ m₀ * Z ^ m₀ * Real.exp (2 * sz) at hchart
  have hPow : H (L g₂) ^ (j + l) ≤ C₃ ^ (j + l) * U ^ m * Z ^ m * Real.exp (2 * (j + l : ℕ) * sz) := by
    calc
      _ ≤ (C₃ * U ^ m₀ * Z ^ m₀ * Real.exp (2 * sz)) ^ (j + l) :=
        pow_le_pow_left₀ (zero_le_two.trans (two_le_complexMatrixHeight (Nat.succ_pos r) _))
          ((hL g₂).trans hchart) _
      _ = _ := by
        rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← Real.exp_nat_mul]
        dsimp only [m]
        congr 1
        congr 1
        ring
  have hLead := hΦ (L g₂) g₁.val Y
  have hLead' : ‖Φ ((L g₂).val * leadingInput (Nat.add_sub_of_le hkn.le) g₁.val Y)‖ ≤
      C₀ * (C₃ ^ (j + l) * U ^ m * Z ^ m * Real.exp (2 * (j + l : ℕ) * sz)) *
        matrixDecay j g₁.val * matrixDecay l Y :=
    hLead.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hPow hC₀) (by unfold matrixDecay; positivity))
      (by unfold matrixDecay; positivity))
  have hw := hWJ (1 : G n) (mem_singleton 1) (padGL hkn.le g * g₂⁻¹)
  dsimp only at hw
  rw [mul_one, complexTwoBlockIwasawa n k hk hkn g h₂ X p.2.2.2.2, hy, hz, sum_abs_blockLog] at hw
  have hv := hV₀ g (R g₁)
  simp only [Nat.cast_zero, zero_mul, mul_zero, sub_zero, add_zero, hy] at hv
  have hv' : ‖V.val (g * R g₁)‖ ≤ C₂ * H g₁ ^ M * Real.exp ((N₂ : ℝ) * sy) :=
    hv.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_two.trans (two_le_complexMatrixHeight hk _)) (hR g₁) _) hC₂) (by positivity))
  have hRight : 0 ≤ δ g₁ ^ s := Real.rpow_nonneg (by unfold complexNormalizedAbs; positivity) _
  have hE :
      Real.exp (2 * (j + l : ℕ) * sz) *
        Real.exp ((N₁ : ℝ) * (sy + sz) - (J : ℝ) * rootPos (blockLog hkn y z)) *
        Real.exp ((N₂ : ℝ) * sy) * Real.exp (2 * u * (∑ i, y i)) * Real.exp (b * sz) =
      Real.exp (A * sy + B * sz + (2 * u) * (∑ i, y i) - (J : ℝ) * rootPos (blockLog hkn y z)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp only [A, B]
    ring
  unfold alternateGapNorm
  change ‖Φ ((L g₂).val * leadingInput _ g₁.val Y)‖ * D * ‖W.val (padGL hkn.le g * g₂⁻¹)‖ *
    ‖V.val (g * R g₁)‖ * δ g ^ u * δ g₁ ^ s * Real.exp (b * sz) ≤ _
  rw [hδ]
  calc
    _ ≤ (C₀ * (C₃ ^ (j + l) * U ^ m * Z ^ m * Real.exp (2 * (j + l : ℕ) * sz)) *
        matrixDecay j g₁.val * matrixDecay l Y) * D *
        (C₁ * Real.exp ((N₁ : ℝ) * (sy + sz) - (J : ℝ) * rootPos (blockLog hkn y z))) *
        (C₂ * H g₁ ^ M * Real.exp ((N₂ : ℝ) * sy)) *
        Real.exp (2 * u * (∑ i, y i)) * δ g₁ ^ s * Real.exp (b * sz) := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hLead' (norm_nonneg _))
          hw (norm_nonneg _) ?_) hv' (norm_nonneg _) ?_) (Real.exp_nonneg _)) hRight) (Real.exp_nonneg _)
      all_goals dsimp only [U, Z, D, matrixDecay]; positivity
    _ = (C₀ * C₁ * C₂ * C₃ ^ (j + l)) * weightedMatrixTail M j s g₁ * matrixDecay l Y *
      (D * U ^ m * Z ^ m) *
      (Real.exp (2 * (j + l : ℕ) * sz) *
        Real.exp ((N₁ : ℝ) * (sy + sz) - (J : ℝ) * rootPos (blockLog hkn y z)) *
        Real.exp ((N₂ : ℝ) * sy) * Real.exp (2 * u * (∑ i, y i)) * Real.exp (b * sz)) := by
      unfold weightedMatrixTail
      ring
    _ = _ := by
      rw [hE]
      change _ = (C₀ * C₁ * C₂ * C₃ ^ (j + l)) * weightedMatrixTail M j s g₁ * matrixDecay l Y *
        (D * U ^ m * Z ^ m *
          Real.exp (A * sy + B * sz + (2 * u) * (∑ i, y i) - (J : ℝ) * rootPos (blockLog hkn y z)))
      ring

end Langlands.Global.RankinSelbergGlobal.ComplexGapAlternateMajorant
