import Langlands.Global.RankinSelberg.RealGapAlternateTailBound
import Langlands.Global.RankinSelberg.RealGapAlternateHaarDecay
import Langlands.Global.RankinSelberg.RealGapOrdinaryMajorant
import Langlands.Global.RankinSelberg.RealLocalEqualFamily

/-! # Joint absolute convergence in the alternate real gap chart -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap ENNReal NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapAlternateConvergence

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (rankInclusion)
open Langlands.HarmonicAnalysis (rowMeasure)
open Langlands.QuotientIntegration (leftQuotient_isOpenQuotientMap)
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ArchimedeanLocal (RealQuotientMeasureData realNormalizedAbs realSelfDualMeasure)
open RealGapAlternateColumnDecay (unipotentDecay)
open RealGapAlternateHaarDecay (diagonalGrowth diagonalGrowth_nonneg diagonalDecay realGapAlternateHaarDecay)
open RealGapAlternateRetained (alpha_rankInclusion_mul_retained_inv firstRetainedColumn lastRetainedInverseRow)
open RealGapAlternateTailBound (headDecay sum_abs_append realGapAlternateTailBound)
open RealGapColumnFourier (triangularFourier)
open RealGapLeadingSchwartz (leadingStack realGapLeadingSchwartz matrixDecay weightedMatrixTail exists_integrable_weightedMatrixTail)
open RealGapOrdinaryMajorant (normalizedDet_eq_exp)
open RealGapTriangularChart (Outer retainedMatrix outerMeasure diagonalWeightMeasure)
open RealJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)
open RealIwasawa (alpha alphaQ alphaQ_mk continuous_alphaQ)
open RealPlaceRestriction (two_le_realMatrixHeight)
open RealWhittakerTranslateBound (realWhittakerTranslateBound)
open RealWhittakerTranslatedMellin (HasGaugeBound)
open RealConvergenceAnalysis (lintegral_exp_neg_mul_sum_abs_lt_top rootPos)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "KU" => fun n => unitaryCompact ℝ n
local notation "U" => fun n => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "Q" => fun t => LeftUnipotentQuotient t ℝ
local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℝ
local notation "YMat" => fun t q => Mat (q + 1) (t + 1)
local notation "Size" => fun t q => (t + 1) + q + 1
local notation "Coords" => fun t q => Q t × (YMat t q × (Outer (t + 1) q × U (q + 1)))
local notation "δ" => fun g => realNormalizedAbs (Matrix.det (Units.val g))
local notation "H" => realMatrixHeight

local instance gapAlternateConvGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapAlternateConvGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance gapAlternateConvGLSecondCountable (n : ℕ) : SecondCountableTopology (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).isInducing.secondCountableTopology
local instance gapAlternateConvGLLocallyCompact (n : ℕ) : LocallyCompactSpace (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).locallyCompactSpace
local instance gapAlternateConvUMeasurable (n : ℕ) : MeasurableSpace (U n) := borel _
local instance gapAlternateConvUBorel (n : ℕ) : BorelSpace (U n) := ⟨rfl⟩

local instance gapAlternateConvQMeasurable (n : ℕ) : MeasurableSpace (Q n) := borel _
local instance gapAlternateConvQBorel (n : ℕ) : BorelSpace (Q n) := ⟨rfl⟩

/-- The compatible quotient, leading lower rectangle, and genuine triangular chart measures. -/
def alternateGapMeasure (t q : ℕ) (a : ℝˣ) (D : RealQuotientMeasureData t)
    (νY : Measure (YMat t q)) (η₁ : Measure (G (t + 1))) (κ : Measure (KU (Size t q))) :
    Measure (Coords t q) :=
  let μ := realSelfDualMeasure a
  D.measure.prod (νY.prod ((outerMeasure (t + 1) q μ η₁ κ).prod (entryHaar μ (q + 1))))

private def quotientDecay {t : ℕ} (B : ℝ) (u : Q t) : ℝ :=
  Real.exp (-(B + 1) * ∑ i, |alphaQ u i|)

private theorem integrable_quotientDecay {t : ℕ} (D : RealQuotientMeasureData t)
    (c : ℝ≥0) (L : (Fin (t + 1) → ℝ) →L[ℝ] ℝ)
    (hL : ∀ F : (Fin (t + 1) → ℝ) → ℝ≥0∞, Measurable F →
      ∫⁻ u, F (alphaQ u) ∂D.measure = (c : ℝ≥0∞) * ∫⁻ y, ENNReal.ofReal (Real.exp (L y)) * F y) :
    Integrable (quotientDecay ‖L‖) D.measure := by
  let F := fun y : Fin (t + 1) → ℝ => Real.exp (-(‖L‖ + 1) * ∑ i, |y i|)
  have hS : Continuous (fun y : Fin (t + 1) → ℝ => ∑ i, |y i|) :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).abs
  have hF : Continuous F := Real.continuous_exp.comp (continuous_const.mul hS)
  refine ⟨(hF.comp continuous_alphaQ).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  change ∫⁻ u, ENNReal.ofReal ‖F (alphaQ u)‖ ∂D.measure < ⊤
  simp_rw [show ∀ u : Q t, ‖F (alphaQ u)‖ = F (alphaQ u) from fun _ => Real.norm_of_nonneg (Real.exp_nonneg _)]
  let f := fun y => ENNReal.ofReal (F y)
  change ∫⁻ u, f (alphaQ u) ∂D.measure < ⊤
  rw [hL f (ENNReal.measurable_ofReal.comp hF.measurable)]
  apply ENNReal.mul_lt_top ENNReal.coe_lt_top
  calc
    _ ≤ ∫⁻ y : Fin (t + 1) → ℝ, ENNReal.ofReal (Real.exp (-1 * ∑ i, |y i|)) := by
      refine lintegral_mono fun y => ?_
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      dsimp only [f, F]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hy := RealEqualConvergence.linear_le L y
      linarith
    _ < ⊤ := lintegral_exp_neg_mul_sum_abs_lt_top one_pos

private theorem integrable_headDecay (k m : ℕ) (a : ℝˣ) (hm : Module.finrank ℝ (Fin k → ℝ) < m) :
    Integrable (headDecay m : (Fin k → ℝ) → ℝ) (rowMeasure (realSelfDualMeasure a) k) := by
  let μ := realSelfDualMeasure a
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  refine (integrable_one_add_norm (μ := rowMeasure μ k) (r := (m : ℝ)) (by exact_mod_cast hm)).congr ?_
  exact ae_of_all _ fun x => by
    change (1 + ‖x‖) ^ (-(m : ℝ)) = ((1 + ‖x‖) ^ m)⁻¹
    rw [Real.rpow_neg (by positivity : 0 ≤ 1 + ‖x‖), Real.rpow_natCast]

/-- The alternate split kernel norm with independent leading determinant exponents and
an arbitrary fixed exponential in the logarithmic tail. -/
def alternateGapNorm {t q : ℕ} (a : ℝˣ) (Φ₀ : 𝓢(Mat (Size t q) (t + 1), ℂ))
    (Φ Ψ : 𝓢((Fin (Size t q) → ℝ), ℂ)) (Ξ : Fin q → 𝓢((Fin (Size t q) → ℝ), ℂ))
    (W : G (Size t q) → ℂ) (V : G (t + 1) → ℂ) (u s b : ℝ)
    (g z₁ : G (t + 1)) (B₁ : G (Size t q)) (Y : YMat t q) (p : Outer (t + 1) q) (Z : U (q + 1)) : ℝ :=
  let B := retainedMatrix (t + 1) q p
  let z := p.1.1.1
  ‖Φ₀ (B₁.val * leadingStack z.val Y)‖ * ‖Φ (firstRetainedColumn p)‖ * ‖Ψ (lastRetainedInverseRow p)‖ *
    ‖triangularFourier (t + 1) q a B Ξ Z‖ * ‖W (rankInclusion (q + 1) g * B⁻¹)‖ * ‖V (g * z₁)‖ *
    δ g ^ u * δ z ^ s * Real.exp (b * ∑ i, |p.1.1.2 i|)

/-- Joint convergence against the actual alternate chart, allowing either additive Haar or
restriction to the zero lower rectangle and either choice of inverse-transpose multiplier. -/
def RealGapAlternateConvergenceStatement : Prop :=
  ∀ (t q : ℕ) (a : ℝˣ) (W : G (Size t q) → ℂ) (V : G (t + 1) → ℂ),
    HasGaugeBound W → HasGaugeBound V →
    ∀ (D : RealQuotientMeasureData t) (νY : Measure (YMat t q)) (η₁ : Measure (G (t + 1)))
      (κ : Measure (KU (Size t q))),
    η₁.IsHaarMeasure → κ.IsHaarMeasure → SigmaFinite νY → ∀ l : ℕ, Integrable (matrixDecay l) νY →
    ∃ σ τ : ℝ, ∀ (u s b : ℝ), σ ≤ u → τ ≤ s → 0 ≤ b →
      ∀ (Φ₀ : 𝓢(Mat (Size t q) (t + 1), ℂ)) (Φ Ψ : 𝓢((Fin (Size t q) → ℝ), ℂ))
        (Ξ : Fin q → 𝓢((Fin (Size t q) → ℝ), ℂ)) (C : ℝ), 0 ≤ C →
      ∀ (B₁ : Outer (t + 1) q → G (Size t q)) (z₁ : Outer (t + 1) q → G (t + 1)),
      (∀ p, H (B₁ p) ≤ H (retainedMatrix (t + 1) q p)) → (∀ p, H (z₁ p) ≤ H p.1.1.1) →
      ∀ (F : Coords t q → ℂ),
      let μ := alternateGapMeasure t q a D νY η₁ κ
      AEStronglyMeasurable F μ →
      (∀ v, ‖F v‖ ≤ C * alternateGapNorm a Φ₀ Φ Ψ Ξ W V u s b v.1.out
        (z₁ v.2.2.1) (B₁ v.2.2.1) v.2.1 v.2.2.1 v.2.2.2) → Integrable F μ

set_option maxHeartbeats 1400000 in
theorem realGapAlternateConvergence : RealGapAlternateConvergenceStatement := by
  intro t q a W V hWg hVg D νY η₁ κ hη₁ hκ hνY l hY
  let k := t + 1
  let n := k + q + 1
  let μ := realSelfDualMeasure a
  let : κ.IsHaarMeasure := hκ
  let : η₁.IsHaarMeasure := hη₁
  let : SigmaFinite νY := hνY
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let νZ := entryHaar μ (q + 1)
  let ρ := outerMeasure k q μ η₁ κ
  let : SigmaFinite νZ := entryHaar_sigmaFinite μ (q + 1)
  let : SigmaFinite η₁ := inferInstance
  let : SigmaFinite (diagonalWeightMeasure k q) := inferInstance
  let : SigmaFinite (rowMeasure μ k) := inferInstance
  let : SigmaFinite κ := inferInstance
  let : SigmaFinite ρ := inferInstanceAs (SigmaFinite
    (((η₁.prod (diagonalWeightMeasure k q)).prod κ).prod (rowMeasure μ k)))
  let : SigmaFinite (ρ.prod νZ) := inferInstance
  let : SigmaFinite (νY.prod (ρ.prod νZ)) := inferInstance
  have := D.groupHaar_isHaar
  have := D.unipotentHaar_isHaar
  obtain ⟨c, L, hL⟩ :=
    RealIwasawa.exists_lintegral_alphaQ D.groupHaar D.unipotentHaar D.measure D.compatible
  have hQ := integrable_quotientDecay D c L hL
  have hD := realGapAlternateHaarDecay k q
  let m := Module.finrank ℝ (Fin k → ℝ) + 1
  have hX := integrable_headDecay k m a (Nat.lt_succ_self _)
  have hK : Integrable (fun _ : KU n => (1 : ℝ)) κ := integrable_const 1
  obtain ⟨N, hW⟩ := hWg
  obtain ⟨N', hV⟩ := realWhittakerTranslateBound t V hVg
  obtain ⟨CV, hCV, hV₀⟩ := hV 0
  let M := N' * k
  let A : ℝ := N + N' + ‖L‖
  refine ⟨A + 1, (k : ℝ) + 2 * M, fun u s b hu hs hb Φ₀ Φ Ψ Ξ C hC B₁ z₁ hB₁ hz₁ F hF hFb => ?_⟩
  obtain ⟨j, hj⟩ := exists_integrable_weightedMatrixTail t M η₁ s hs
  obtain ⟨CLead, hCLead, hΦ⟩ := realGapLeadingSchwartz k (q + 1) (Nat.succ_pos _) Φ₀ j l
  let B : ℝ := (N : ℝ) + b + diagonalGrowth k q
  have hB : 0 ≤ B := add_nonneg (add_nonneg (Nat.cast_nonneg _) hb) (diagonalGrowth_nonneg k q)
  have hu' : A + 1 ≤ u := hu
  obtain ⟨J, lZ, CTail, hCTail, hZ, hTail⟩ := realGapAlternateTailBound k q A B u hB hu'
    a Φ Ψ Ξ (j + l) m
  obtain ⟨CW, hCW, hWJ⟩ := hW J
  let C' := C * (CLead * CV * CW * CTail)
  have hProd := (hQ.mul_prod (hY.mul_prod ((((hj.mul_prod hD).mul_prod hK).mul_prod hX).mul_prod hZ))).const_mul C'
  change Integrable F (alternateGapMeasure t q a D νY η₁ κ)
  refine hProd.mono' hF (ae_of_all _ fun v => ?_)
  let g := v.1.out
  let Y := v.2.1
  let p := v.2.2.1
  let Z := v.2.2.2
  let z := p.1.1.1
  let R := retainedMatrix k q p
  let y := alpha g
  let Sy := ∑ i, |y i|
  let Sz := ∑ i, |p.1.1.2 i|
  let sY := ∑ i, y i
  let rPos := rootPos (Fin.append (m := k) (n := q + 1) y (-p.1.1.2))
  let e₁ := (N : ℝ) * (Sy + Sz) - (J : ℝ) * rPos
  let e₂ := (N' : ℝ) * Sy
  let e := A * Sy + B * Sz + u * sY - (J : ℝ) * rPos
  let X₀ := ‖Φ (firstRetainedColumn p)‖ * ‖Ψ (lastRetainedInverseRow p)‖ * ‖triangularFourier k q a R Ξ Z‖
  have hX₀ : 0 ≤ X₀ := by dsimp only [X₀]; positivity
  have hW' := hWJ (rankInclusion (q + 1) g * R⁻¹)
  rw [alpha_rankInclusion_mul_retained_inv] at hW'
  have hsAbs := sum_abs_append y (-p.1.1.2)
  simp only [Pi.neg_apply, abs_neg] at hsAbs
  have hW'' : ‖W (rankInclusion (q + 1) g * R⁻¹)‖ ≤ CW * Real.exp e₁ := by
    refine hW'.trans_eq ?_
    change CW * Real.exp (-(J : ℝ) * rPos +
      (N : ℝ) * (∑ i : Fin (k + (q + 1)), |Fin.append y (-p.1.1.2) i|)) = _
    rw [hsAbs]
    congr 2
    ring
  have hV' := hV₀ g (z₁ p)
  simp only [Nat.cast_zero, zero_mul, mul_zero, sub_zero, add_zero] at hV'
  have hV'' : ‖V (g * z₁ p)‖ ≤ CV * H z ^ M * Real.exp e₂ := by
    refine hV'.trans ?_
    have hz₁₀ : 0 ≤ H (z₁ p) := zero_le_two.trans (two_le_realMatrixHeight (Nat.succ_pos _) _)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz₁₀ (hz₁ p) _) hCV)
      (Real.exp_nonneg _)
  have hΦ' := hΦ (B₁ p) z.val Y
  have hΦ'' : ‖Φ₀ ((B₁ p).val * leadingStack z.val Y)‖ ≤ CLead * H R ^ (j + l) * matrixDecay j z.val * matrixDecay l Y := by
    unfold matrixDecay
    rw [mul_assoc (CLead * H R ^ (j + l)), ← mul_inv, ← div_eq_mul_inv]
    refine hΦ'.trans ?_
    have hB₁₀ : 0 ≤ H (B₁ p) := zero_le_two.trans (two_le_realMatrixHeight (Nat.succ_pos _) _)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB₁₀ (hB₁ p) _) hCLead)
      (by positivity)
  have hg : δ g ^ u = Real.exp (u * sY) := by
    rw [normalizedDet_eq_exp, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    dsimp only [sY, y]
    ring
  have hδz : 0 < δ z := abs_pos.mpr z.det_ne_zero
  have hδs := Real.rpow_nonneg hδz.le s
  have hR : 0 ≤ H R := zero_le_two.trans (two_le_realMatrixHeight (Nat.succ_pos _) R)
  have hHz : 0 ≤ H z := zero_le_two.trans (two_le_realMatrixHeight (Nat.succ_pos _) z)
  have hY' : 0 ≤ matrixDecay l Y := by unfold matrixDecay; positivity
  have hz' : 0 ≤ matrixDecay j z.val := by unfold matrixDecay; positivity
  have hWM : 0 ≤ weightedMatrixTail M j s z := by unfold weightedMatrixTail; positivity
  have hExp : Real.exp e₁ * Real.exp e₂ * Real.exp (u * sY) * Real.exp (b * Sz) =
      Real.exp (-‖L‖ * Sy) * Real.exp (-diagonalGrowth k q * Sz) * Real.exp e := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp only [e₁, e₂, e, A, B]
    ring
  have hDom := hTail y p Z
  change H R ^ (j + l) * ‖Φ (firstRetainedColumn p)‖ * ‖Ψ (lastRetainedInverseRow p)‖ *
    ‖triangularFourier k q a R Ξ Z‖ * Real.exp e ≤ _ at hDom
  have hDom' : H R ^ (j + l) * X₀ * Real.exp e ≤
      CTail * Real.exp (-Sy) * Real.exp (-Sz) * headDecay m p.2 * unipotentDecay lZ Z := by
    rw [show H R ^ (j + l) * X₀ = H R ^ (j + l) * ‖Φ (firstRetainedColumn p)‖ *
      ‖Ψ (lastRetainedInverseRow p)‖ * ‖triangularFourier k q a R Ξ Z‖ by dsimp only [X₀]; ring]
    exact hDom
  have hRep : alphaQ v.1 = y := by
    conv_lhs => rw [← Quotient.out_eq v.1]
    exact alphaQ_mk _
  refine (hFb v).trans ?_
  have hNorm : alternateGapNorm a Φ₀ Φ Ψ Ξ W V u s b g (z₁ p) (B₁ p) Y p Z =
      ‖Φ₀ ((B₁ p).val * leadingStack z.val Y)‖ * X₀ * ‖W (rankInclusion (q + 1) g * R⁻¹)‖ *
      ‖V (g * z₁ p)‖ * δ g ^ u * δ z ^ s * Real.exp (b * Sz) := by
    dsimp only [alternateGapNorm, X₀, Sz, R, z]
    ring
  rw [hNorm, hg]
  calc
    _ = C * ‖Φ₀ ((B₁ p).val * leadingStack z.val Y)‖ * X₀ *
        ‖W (rankInclusion (q + 1) g * R⁻¹)‖ * ‖V (g * z₁ p)‖ *
        Real.exp (u * sY) * δ z ^ s * Real.exp (b * Sz) := by ring
    _ ≤ C * (CLead * H R ^ (j + l) * matrixDecay j z.val * matrixDecay l Y) * X₀ *
        (CW * Real.exp e₁) * (CV * H z ^ M * Real.exp e₂) * Real.exp (u * sY) * δ z ^ s * Real.exp (b * Sz) := by
      gcongr
    _ = (C * CLead * CV * CW * weightedMatrixTail M j s z * matrixDecay l Y * H R ^ (j + l) * X₀) *
        (Real.exp e₁ * Real.exp e₂ * Real.exp (u * sY) * Real.exp (b * Sz)) := by
      unfold weightedMatrixTail
      ring
    _ = (C * CLead * CV * CW * weightedMatrixTail M j s z * matrixDecay l Y *
          Real.exp (-‖L‖ * Sy) * Real.exp (-diagonalGrowth k q * Sz)) *
          (H R ^ (j + l) * X₀ * Real.exp e) := by rw [hExp]; ring
    _ ≤ (C * CLead * CV * CW * weightedMatrixTail M j s z * matrixDecay l Y *
          Real.exp (-‖L‖ * Sy) * Real.exp (-diagonalGrowth k q * Sz)) *
          (CTail * Real.exp (-Sy) * Real.exp (-Sz) * headDecay m p.2 * unipotentDecay lZ Z) :=
      mul_le_mul_of_nonneg_left hDom' (by positivity)
    _ = _ := by
      dsimp only [C', quotientDecay, diagonalDecay]
      rw [hRep, mul_one]
      have he₁ : Real.exp (-‖L‖ * Sy) * Real.exp (-Sy) = Real.exp (-(‖L‖ + 1) * Sy) := by
        rw [← Real.exp_add]; congr 1; ring
      have he₂ : Real.exp (-diagonalGrowth k q * Sz) * Real.exp (-Sz) = diagonalDecay k q p.1.1.2 := by
        unfold diagonalDecay
        rw [← Real.exp_add]; congr 1; dsimp only [Sz]; ring
      change _ = C' * (Real.exp (-(‖L‖ + 1) * Sy) *
        (matrixDecay l Y * ((weightedMatrixTail M j s z * diagonalDecay k q p.1.1.2 * headDecay m p.2) * unipotentDecay lZ Z)))
      rw [← he₁, ← he₂]
      dsimp only [C']
      ring

end Langlands.Global.RankinSelbergGlobal.RealGapAlternateConvergence
