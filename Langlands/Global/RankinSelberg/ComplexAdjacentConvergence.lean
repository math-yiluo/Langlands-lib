import Langlands.Global.RankinSelberg.ComplexAdjacentUnfolding
import Langlands.Global.RankinSelberg.ComplexLastRowSchwartz
import Langlands.Global.RankinSelberg.ComplexLocalEqualHolomorphy
import Langlands.Global.RankinSelberg.ComplexLocalOrdinaryConvergence
import Langlands.Global.RankinSelberg.ComplexSquareZetaConvergence

/-! # Absolute convergence of the unfolded adjacent-rank complex kernel -/

noncomputable section

open MeasureTheory Topology
open scoped Matrix.Norms.Operator NNReal ENNReal SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding

open ArchimedeanLocal (ComplexQuotientMeasureData complexNormalizedAbs)
open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.QuotientIntegration
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ComplexLocalIwasawa (alpha alphaQ alphaQ_mk continuous_alphaQ kpart mk_eq_mk_logTorus_mul_kpart)
open ComplexLocalWhittakerGauge (logTorus height_logTorus_mul_le)
open ComplexLocalOrdinaryConvergence (norm_detPower_logTorus_mul)
open ComplexGodement (normPower characterWeight continuous_characterWeight norm_characterWeight)
open ComplexLastRowSchwartz (complexLastRowSchwartz)
open RealConvergenceAnalysis (rootPos exponent_le lintegral_exp_neg_mul_sum_abs_lt_top)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear r.succ ℂ
local notation "N" => Langlands.GeneralLinear.upperUnipotent r.succ ℂ
local notation "K" => unitaryCompact ℂ r.succ
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "Mat" => Matrix (Fin r.succ) (Fin r.succ) ℂ
local notation "Vec" => Fin r.succ → ℂ
local notation "Y" => Fin r.succ → ℝ

private theorem unfoldedKernel_mk (d : ComplexCharacterData) (p s : ℂ) (Φ : Mat → ℂ) (φ : Vec → ℂ)
    {W V : G → ℂ} {a : ℂˣ} {ds es : List ComplexCharacterData} (hW : W ∈ complexWhittakerModel r ds a)
    (hV : V ∈ complexWhittakerModel r es (-a)) (h g : G) :
    unfoldedKernel d p s Φ φ W V (h, leftQuotientMap N g) =
      Φ h.val * characterWeight d (p + s) (determinant h) *
        (W g * V (g * h) * φ (Langlands.RankinSelberg.lastRow g) *
          ArchimedeanLocal.detPower complexNormalizedAbs g s) := by
  have hpair (u : N) (x : G) : W (u.val * x) * V ((u.val * x) * h) = W x * V (x * h) := by
    rw [mul_assoc u.val x h, complexWhittakerModel_left_equivariant hW u.val u.2,
      complexWhittakerModel_left_equivariant hV u.val u.2,
      mul_mul_mul_comm, ComplexCharacterChange.whittakerCharacter_neg_parameter, one_mul]
  unfold unfoldedKernel
  exact congrArg (Φ h.val * characterWeight d (p + s) (determinant h) * ·)
    (EqualIntegrandProducts.equalIntegrand_mk_of_pair_invariant complexNormalizedAbs r W
      (fun x => V (x * h)) hpair φ s g)

private theorem continuous_unfoldedKernel (d : ComplexCharacterData) (p s : ℂ)
    (Φ : 𝓢(Mat, ℂ)) (φ : 𝓢(Vec, ℂ)) {W V : G → ℂ} {a : ℂˣ} {ds es : List ComplexCharacterData}
    (hW : W ∈ complexWhittakerModel r ds a) (hV : V ∈ complexWhittakerModel r es (-a)) :
    Continuous (unfoldedKernel d p s Φ φ W V) := by
  have HQ := leftQuotient_isOpenQuotientMap N
  rw [← (IsOpenQuotientMap.id.prodMap HQ).continuous_comp_iff]
  have hEq : unfoldedKernel d p s Φ φ W V ∘ Prod.map id (leftQuotientMap N) =
      fun x : G × G => Φ x.1.val * characterWeight d (p + s) (determinant x.1) *
        (W x.2 * V (x.2 * x.1) * φ (Langlands.RankinSelberg.lastRow x.2) *
          ArchimedeanLocal.detPower complexNormalizedAbs x.2 s) :=
    funext fun x => unfoldedKernel_mk d p s Φ φ hW hV x.1 x.2
  rw [hEq]
  have hw := (contMDiff_of_mem_complexWhittakerModel hW).continuous
  have hv := (contMDiff_of_mem_complexWhittakerModel hV).continuous
  have hr : Continuous (Langlands.RankinSelberg.lastRow : G → Vec) :=
    continuous_pi fun j => Units.continuous_val.matrix_elem (Fin.last r) j
  have hlog : Continuous (fun g : G => Real.log (complexNormalizedAbs g.val.det)) :=
    continuous_complexQuotientLogDet.comp HQ.continuous
  have hp : Continuous (fun g : G => ArchimedeanLocal.detPower complexNormalizedAbs g s) :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hlog))
  exact ((Φ.continuous.comp (Units.continuous_val.comp continuous_fst)).mul
    ((continuous_characterWeight d (p + s)).comp
      (Matrix.GeneralLinearGroup.continuous_det.comp continuous_fst))).mul
    ((((hw.comp continuous_snd).mul (hv.comp (continuous_snd.mul continuous_fst))).mul
      (φ.continuous.comp (hr.comp continuous_snd))).mul (hp.comp continuous_snd))

private theorem toral_envelope_integrable (D : ComplexQuotientMeasureData r)
    (κ : ℝ≥0) (L : Y →L[ℝ] ℝ)
    (hκL : ∀ B : Y → ℝ≥0∞, Measurable B → ∫⁻ q, B (alphaQ q) ∂D.measure =
      (κ : ℝ≥0∞) * ∫⁻ y, ENNReal.ofReal (Real.exp (L y)) * B y) :
    Integrable (fun q : Q => Real.exp (-(∑ i, |alphaQ q i|) - L (alphaQ q))) D.measure := by
  let S (y : Y) : ℝ := ∑ i, |y i|
  have hS : Continuous S := continuous_finsetSum _ fun i _ => (continuous_apply i).abs
  let B (y : Y) := ENNReal.ofReal (Real.exp (-S y - L y))
  have hB : Continuous (fun y : Y => Real.exp (-S y - L y)) :=
    Real.continuous_exp.comp (hS.neg.sub L.continuous)
  refine ⟨(hB.comp continuous_alphaQ).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_of_nonneg (Real.exp_nonneg _)]
  change (∫⁻ q, B (alphaQ q) ∂D.measure) < ∞
  rw [hκL B (ENNReal.measurable_ofReal.comp hB.measurable)]
  have hE (y : Y) : ENNReal.ofReal (Real.exp (L y)) * B y = ENNReal.ofReal (Real.exp (-1 * S y)) := by
    dsimp only [B]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  simp_rw [hE]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (lintegral_exp_neg_mul_sum_abs_lt_top one_pos)

private theorem height_nonneg (g : G) : 0 ≤ complexMatrixHeight g := by
  unfold complexMatrixHeight
  positivity

/-- The complete kernel in Jacquet's adjacent-rank unfolding is absolutely integrable on a
right half-plane. The estimate is uniform in the group variable of the inner coefficient. -/
def ComplexAdjacentConvergenceStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) [SFinite D.measure] (ν : Measure G) [ν.IsHaarMeasure] [SFinite ν]
    (d : ComplexCharacterData) (p : ℂ) (Φ : 𝓢(Mat, ℂ)) (φ : 𝓢(Vec, ℂ)) (a : ℂˣ)
    (ds es : List ComplexCharacterData) (W : complexWhittakerModel r ds a)
    (V : complexWhittakerModel r es (-a)),
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (unfoldedKernel d p s Φ φ W.val V.val) (ν.prod D.measure)

set_option maxHeartbeats 800000 in
theorem complexAdjacentConvergence : ComplexAdjacentConvergenceStatement (r := r) := by
  intro D _ ν _ _ d p Φ φ a ds es W V
  obtain ⟨κ, L, hκL⟩ := complexIwasawaToralMeasure r D
  obtain ⟨B, hB⟩ := complexWhittakerSimpleRootMajorization r ds a W
  obtain ⟨C₂, M, hC₂, hV⟩ := complexWhittakerModel_moderateGrowth V.2
  let A : ℝ := (B : ℝ) + 2 * (M : ℝ) + ‖L‖
  let σ₁ : ℝ := (r.succ : ℝ) + M - (p + d.exponent).re
  let σ₂ : ℝ := (A + 1) * ((r : ℝ) + 1) / 2
  refine ⟨max σ₁ σ₂, fun s hs => ?_⟩
  let t : ℝ := 2 * s.re
  have ht : (A + 1) * ((r : ℝ) + 1) ≤ t := by
    have := (le_max_right σ₁ σ₂).trans_lt hs
    dsimp [σ₂, t] at *
    linarith
  obtain ⟨J, hJ⟩ := exists_nat_gt ((A + 1) * ((r : ℝ) + 1) + t * ((r : ℝ) + 1))
  obtain ⟨C₁, hC₁, hW⟩ := hB J []
  obtain ⟨C₃, hC₃, hφ⟩ := complexLastRowSchwartz φ J
  let H₀ : ℝ := 1 + 2 * (r.succ : ℝ) ^ 2
  let C : ℝ := C₁ * C₂ * H₀ ^ M * C₃
  let S (y : Y) : ℝ := ∑ i, |y i|
  let Q₀ (q : Q) := C * Real.exp (-S (alphaQ q) - L (alphaQ q))
  let P₀ (h : G) := ‖(complexMatrixHeight h ^ M : ℝ) * Φ h.val * normPower
    (d.exponent + (p + s)) (determinant h)‖
  have hQ : Integrable Q₀ D.measure := (toral_envelope_integrable D κ L hκL).const_mul C
  have hP : Integrable P₀ ν := by
    apply (ComplexSquareZeta.integrable_height_detNormPower ν M Φ (d.exponent + (p + s)) ?_).norm
    have := (le_max_left σ₁ σ₂).trans_lt hs
    simp only [Complex.add_re] at *
    dsimp [σ₁] at *
    linarith
  have hP_eq (h : G) : P₀ h = ‖Φ h.val‖ * ‖characterWeight d (p + s) (determinant h)‖ *
      complexMatrixHeight h ^ M := by
    have hA : 0 < complexNormalizedAbs h.val.det := pow_pos (norm_pos_iff.mpr h.det_ne_zero) _
    have hdet : (determinant h : ℂ) = h.val.det := rfl
    have hpow : ‖normPower (d.exponent + (p + s)) (determinant h)‖ =
        complexNormalizedAbs h.val.det ^ (d.exponent + (p + s)).re := by
      exact Complex.norm_cpow_eq_rpow_re_of_pos hA _
    simp only [P₀, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (height_nonneg h) _), hpow, norm_characterWeight, hdet]
    ring
  have hV₀ (g : G) : ‖V.val g‖ ≤ C₂ * complexMatrixHeight g ^ M := by
    have h := (show (1 : ℝ) ≤ 2 by norm_num).trans
      (ComplexPlaceAnalytic.two_le_complexMatrixHeight (Nat.succ_pos r) g)
    simpa only [max_eq_right h] using hV g
  have hV_bound (y : Y) (k : K) (h : G) :
      ‖V.val (logTorus y * k.val * h)‖ ≤
        C₂ * (H₀ ^ M * Real.exp (2 * (M : ℝ) * S y)) * complexMatrixHeight h ^ M := by
    let g := logTorus y * k.val
    have hg : complexMatrixHeight g ≤ H₀ * Real.exp (2 * S y) :=
      (le_max_right _ _).trans (height_logTorus_mul_le y k)
    have hmul : complexMatrixHeight (g * h) ≤ H₀ * Real.exp (2 * S y) * complexMatrixHeight h :=
      (ComplexCharacterChange.complexMatrixHeight_mul_le g h).trans
        (mul_le_mul_of_nonneg_right hg (height_nonneg h))
    calc
      _ ≤ C₂ * (H₀ * Real.exp (2 * S y) * complexMatrixHeight h) ^ M :=
        (hV₀ (g * h)).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (height_nonneg _) hmul _) hC₂)
      _ = _ := by
        rw [mul_pow, mul_pow, ← Real.exp_nat_mul,
          show (M : ℝ) * (2 * S y) = 2 * (M : ℝ) * S y by ring]
        ring
  have hExp (y : Y) :
      (B : ℝ) * S y - (J : ℝ) * rootPos y + 2 * (M : ℝ) * S y -
        (J : ℝ) * max (y (Fin.last r)) 0 + t * ∑ i, y i ≤ -S y - L y := by
    have hSL : ‖y‖ ≤ S y := by
      apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg (y i))).2
      intro i
      simpa only [Real.norm_eq_abs] using
        (Finset.single_le_sum (fun j _ => abs_nonneg (y j)) (Finset.mem_univ i) : |y i| ≤ S y)
    have hL := (le_abs_self (L y)).trans ((L.le_opNorm y).trans
      (mul_le_mul_of_nonneg_left hSL (norm_nonneg _)))
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have he := exponent_le y hA ht hJ.le hJ.le
    change -(J : ℝ) * rootPos y + A * S y + t * ∑ i, y i -
      (J : ℝ) * max (y (Fin.last r)) 0 ≤ -S y at he
    dsimp only [A] at he
    linarith
  have hrep (h : G) (y : Y) (k : K) :
      ‖unfoldedKernel d p s Φ φ W.val V.val (h, leftQuotientMap N (logTorus y * k.val))‖ ≤
        P₀ h * (C * Real.exp (-S y - L y)) := by
    let g := logTorus y * k.val
    let E₁ := (B : ℝ) * S y - (J : ℝ) * rootPos y
    let E₂ := 2 * (M : ℝ) * S y
    let E₃ := -(J : ℝ) * max (y (Fin.last r)) 0
    let E₄ := t * ∑ i, y i
    have h₁ : ‖W.val g‖ ≤ C₁ * Real.exp E₁ := by
      simpa only [g, E₁, S, rootPos, List.map_nil, List.prod_nil, Module.End.one_apply] using hW y k
    have h₂ := hV_bound y k h
    have h₃ := hφ y k
    have h₀ : 0 ≤ H₀ := by dsimp [H₀]; positivity
    have hH := height_nonneg h
    rw [unfoldedKernel_mk d p s Φ φ W.2 V.2, norm_mul, norm_mul, norm_mul, norm_mul,
      norm_mul, norm_detPower_logTorus_mul]
    change ‖Φ h.val‖ * ‖characterWeight d (p + s) (determinant h)‖ *
      (‖W.val g‖ * ‖V.val (g * h)‖ * ‖φ (Langlands.RankinSelberg.lastRow g)‖ * Real.exp E₄) ≤ _
    calc
      _ ≤ ‖Φ h.val‖ * ‖characterWeight d (p + s) (determinant h)‖ *
          ((C₁ * Real.exp E₁) * (C₂ * (H₀ ^ M * Real.exp E₂) * complexMatrixHeight h ^ M) *
            (C₃ * Real.exp E₃) * Real.exp E₄) := by
        gcongr
      _ = P₀ h * (C * Real.exp (E₁ + E₂ + E₃ + E₄)) := by
        rw [hP_eq, Real.exp_add, Real.exp_add, Real.exp_add]
        dsimp only [C]
        ring
      _ ≤ _ := by
        gcongr
        dsimp only [E₁, E₂, E₃, E₄]
        simpa only [sub_eq_add_neg, neg_mul] using hExp y
  refine (hP.smul_prod hQ).mono' (continuous_unfoldedKernel d p s Φ φ W.2 V.2).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rcases x with ⟨h, q⟩
  refine Quotient.inductionOn q fun g => ?_
  have hq := mk_eq_mk_logTorus_mul_kpart g
  change ‖unfoldedKernel d p s Φ φ W.val V.val (h, Quotient.mk (QuotientGroup.rightRel N) g)‖ ≤
    P₀ h * (C * Real.exp (-S (alphaQ (Quotient.mk (QuotientGroup.rightRel N) g)) -
      L (alphaQ (Quotient.mk (QuotientGroup.rightRel N) g))))
  rw [alphaQ_mk, hq]
  exact hrep h (alpha g) (kpart g)

end Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding
