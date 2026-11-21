import Langlands.Global.RankinSelberg.ComplexLocalEqualProductBounds
import Langlands.Global.RankinSelberg.ComplexLocalEqualQuotientChange
import Langlands.Global.RankinSelberg.ComplexLocalEqualUnfoldedSign
import Langlands.Global.RankinSelberg.ComplexLocalIwasawaProductMeasure
import Langlands.Global.RankinSelberg.ComplexLocalSquarePositiveWeight

/-! # Joint convergence of the equal-rank double integral for a large adjoining exponent -/

noncomputable section

open MeasureTheory
open Langlands.Archimedean Langlands.Archimedean.ComplexDuality Langlands.GeneralLinear
open Langlands.LocalFactor.Archimedean Langlands.QuotientIntegration
open Langlands.RankinSelberg (LeftUnipotentQuotient unipotent_det)
open scoped ENNReal Manifold ContDiff Matrix.Norms.Operator NNReal SchwartzMap
  Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal ComplexLocalIwasawa
open ComplexLocalWhittakerGauge (logTorus)
open ComplexCharacterChange (model_unipotent_mul whittakerCharacter_neg_parameter)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "Y" => Fin m → ℝ
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "K" => unitaryCompact ℂ m
local notation "N" => Langlands.GeneralLinear.upperUnipotent m ℂ
local notation "NG" => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "pad" => padGL (R := ℂ) (Nat.le_succ m)
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs
local notation "μK" => unitaryHaar m

private theorem pad_mem_upperUnipotent (u : N) : pad u.val ∈ NG := by
  constructor
  · intro i j hij
    change j < i at hij
    rw [UnequalAnalytic.padGL_apply]
    split
    · exact UpperUnipotent.entry_eq_zero u hij
    · exact Matrix.one_apply_ne hij.ne'
  · intro i
    rw [UnequalAnalytic.padGL_apply]
    split
    · exact UpperUnipotent.entry_diag u _
    · exact Matrix.one_apply_eq i

private theorem whittakerCharacter_pad (a : ℂˣ) (u : N) :
    complexWhittakerCharacter a (pad u.val) = complexWhittakerCharacter a u.val := by
  apply congrArg (fun z : ℂ => (complexScaledCharacter a).complex z)
  rw [Fin.sum_univ_castSucc]
  have hlast : (pad u.val).val (Fin.last r).castSucc (Fin.last r).succ = 0 := by
    rw [UnequalAnalytic.padGL_apply, dite_eq_right (by simp)]
    exact Matrix.one_apply_ne (ne_of_lt Fin.castSucc_lt_succ)
  rw [hlast, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [UnequalAnalytic.padGL_apply, dite_eq_left ⟨Nat.lt_succ_of_lt i.isLt, Nat.succ_lt_succ i.isLt⟩]
  rfl

private theorem unfoldedInner_mk {a : ℂˣ} {ds es : List ComplexCharacterData}
    (U : complexWhittakerModel r ds a) (V : complexWhittakerModel (r + 1) es (-a))
    (h : H) (g : G) (s : ℂ) :
    complexEqualUnfoldedInner U.val V.val g s (Quotient.mk _ h) =
      U.val h * V.val (pad h * g) * P h (s - 1 / 2) := by
  let f (x : H) := U.val x * V.val (pad x * g) * P x (s - 1 / 2)
  have hV (u : N) (x : G) :
      V.val (pad u.val * x) = complexWhittakerCharacter (-a) u.val * V.val x := by
    rw [complexWhittakerModel_left_equivariant V.2 _ (pad_mem_upperUnipotent u),
      whittakerCharacter_pad]
  have hf (u : N) (x : H) : f (u.val * x) = f x := by
    simp only [f, map_mul, mul_assoc (pad u.val), model_unipotent_mul U.2 u,
      hV u]
    rw [mul_mul_mul_comm, whittakerCharacter_neg_parameter, one_mul]
    simp only [ArchimedeanLocal.detPower, Units.val_mul, Matrix.det_mul, unipotent_det, one_mul]
  exact congrArg (descend N f hf) (Quotient.out_eq (Quotient.mk _ h))

/-- The equal-rank double kernel for a square matrix test. -/
def complexEqualUnfoldedKernel (d : ComplexCharacterData) (Φ : Mat → ℂ)
    (U : H → ℂ) (V : G → ℂ) (s : ℂ) (p : Q × G) : ℂ :=
  Φ p.2.val * (d.character (determinant p.2) : ℂ) * P p.2 (s + ((m : ℕ) : ℂ) / 2) *
    complexEqualUnfoldedInner U V p.2 s p.1

private theorem continuous_detPower {j : ℕ} (s : ℂ) :
    Continuous (fun g : Langlands.GeneralLinear j ℂ => P g s) := by
  have h : Continuous (fun g : Langlands.GeneralLinear j ℂ => complexNormalizedAbs g.val.det) :=
    Units.continuous_val.matrix_det.norm.pow 2
  have hlog := h.log fun g => pow_ne_zero 2 (norm_ne_zero_iff.mpr g.det_ne_zero)
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hlog))

/-- The equal-rank product kernel descends continuously to the smaller quotient. -/
theorem continuous_complexEqualUnfoldedKernel {a : ℂˣ} {ds es : List ComplexCharacterData}
    (U : complexWhittakerModel r ds a) (V : complexWhittakerModel (r + 1) es (-a))
    (d : ComplexCharacterData) (Φ : 𝓢(Mat, ℂ)) (s : ℂ) :
    Continuous (complexEqualUnfoldedKernel d Φ U.val V.val s) := by
  have hq := leftQuotient_isOpenQuotientMap N
  rw [← (hq.prodMap IsOpenQuotientMap.id).continuous_comp_iff]
  have hForm :
      complexEqualUnfoldedKernel d Φ U.val V.val s ∘ Prod.map (leftQuotientMap N) id =
        fun p : H × G => Φ p.2.val * (d.character (determinant p.2) : ℂ) *
          P p.2 (s + ((m : ℕ) : ℂ) / 2) *
          (U.val p.1 * V.val (pad p.1 * p.2) * P p.1 (s - 1 / 2)) :=
    funext fun p => congrArg (_ * ·) (unfoldedInner_mk U V p.1 p.2 s)
  rw [hForm]
  have hU := (contMDiff_of_mem_complexWhittakerModel U.2).continuous
  have hV := (contMDiff_of_mem_complexWhittakerModel V.2).continuous
  have hχ : Continuous (fun g : G => (d.character (determinant g) : ℂ)) :=
    Units.continuous_val.comp (d.character.continuous.comp determinantContinuous.continuous)
  have hpad : Continuous (pad : H → G) := UnequalAnalytic.continuous_padGL _
  exact (((Φ.continuous.comp Units.continuous_val).comp continuous_snd).mul (hχ.comp continuous_snd)
    |>.mul ((continuous_detPower _).comp continuous_snd)).mul
      (((hU.comp continuous_fst).mul (hV.comp ((hpad.comp continuous_fst).mul continuous_snd))).mul
        ((continuous_detPower _).comp continuous_fst))

private def torusEnvelope (x : Y) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(∑ j, |x j|)))

private theorem measurable_torusEnvelope : Measurable (torusEnvelope (r := r)) :=
  ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp
    ((continuous_finsetSum _ fun j _ => (continuous_apply j).abs).neg)).measurable

private theorem quotient_lintegral_le_shifted (D : ComplexQuotientMeasureData r)
    (c : ℝ≥0) (L : Y →L[ℝ] ℝ)
    (hI : ∀ f : Q → ℝ≥0∞, Measurable f → (∫⁻ q, f q ∂D.measure) =
      (c : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (Real.exp (L x)) *
        (∫⁻ k, f ((quotientHomeomorph m).symm (x, k)) ∂μK))
    (F : Q → ℂ) (hF : Continuous F) (b : ℝ) (hb : 0 ≤ b)
    (v : K → Y) (hv : Measurable v)
    (hBound : ∀ x k, Real.exp (L x) * ‖F ((quotientHomeomorph m).symm (x, k))‖ ≤
      b * Real.exp (-(∑ i, |(x + v k) i|))) :
    (∫⁻ q, ENNReal.ofReal ‖F q‖ ∂D.measure) ≤
      (c : ℝ≥0∞) * (∫⁻ x, torusEnvelope (r := r) x) * ENNReal.ofReal b := by
  let f := fun q => ENNReal.ofReal ‖F q‖
  have hf : Measurable f := ENNReal.measurable_ofReal.comp hF.norm.measurable
  have hE := measurable_torusEnvelope (r := r)
  have hB : Measurable (fun p : Y × K => ENNReal.ofReal b * torusEnvelope (p.1 + v p.2)) :=
    measurable_const.mul (hE.comp (measurable_fst.add (hv.comp measurable_snd)))
  calc
    _ = (c : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (Real.exp (L x)) *
        (∫⁻ k, f ((quotientHomeomorph m).symm (x, k)) ∂μK) := hI f hf
    _ = (c : ℝ≥0∞) * ∫⁻ x, ∫⁻ k, ENNReal.ofReal
        (Real.exp (L x) * ‖F ((quotientHomeomorph m).symm (x, k))‖) ∂μK := by
      congr 1
      refine lintegral_congr fun x => ?_
      simp only [ENNReal.ofReal_mul (Real.exp_nonneg (L x))]
      exact (lintegral_const_mul _ (hf.comp ((quotientHomeomorph m).symm.continuous.comp
        (continuous_const.prodMk continuous_id)).measurable)).symm
    _ ≤ (c : ℝ≥0∞) * ∫⁻ x, ∫⁻ k, ENNReal.ofReal b * torusEnvelope (x + v k) ∂μK := by
      refine mul_le_mul_of_nonneg_left (lintegral_mono fun x => lintegral_mono fun k => ?_) bot_le
      rw [torusEnvelope, ← ENNReal.ofReal_mul hb]
      exact ENNReal.ofReal_le_ofReal (hBound x k)
    _ = (c : ℝ≥0∞) * ∫⁻ k, (∫⁻ x, ENNReal.ofReal b * torusEnvelope (x + v k)) ∂μK := by
      congr 1
      exact lintegral_lintegral_swap (f := fun x k => ENNReal.ofReal b * torusEnvelope (x + v k))
        hB.aemeasurable
    _ = _ := by
      have he (k : K) : (∫⁻ x, ENNReal.ofReal b * torusEnvelope (x + v k)) =
          ENNReal.ofReal b * ∫⁻ x, torusEnvelope (r := r) x := by
        have hf' : Measurable (fun x : Y => torusEnvelope (x + v k)) :=
          hE.comp (measurable_add_const _)
        rw [lintegral_const_mul _ hf']
        exact congrArg ((ENNReal.ofReal b) * ·)
          ((measurePreserving_add_right volume (v k)).lintegral_comp hE)
      simp only [he, lintegral_const, measure_univ, mul_one]
      ac_rfl

/-- The size of the double kernel depends only on the real parts of the two exponents. -/
theorem norm_complexEqualUnfoldedKernel_of_re
    (d d₀ : ComplexCharacterData) (hd : d.exponent.re = d₀.exponent.re)
    (Φ : Mat → ℂ) (U : H → ℂ) (V : G → ℂ) (s s₀ : ℂ) (hs : s.re = s₀.re) (p : Q × G) :
    ‖complexEqualUnfoldedKernel d Φ U V s p‖ = ‖complexEqualUnfoldedKernel d₀ Φ U V s₀ p‖ := by
  simp only [complexEqualUnfoldedKernel, complexEqualUnfoldedInner, norm_mul,
    ComplexSwapJacquet.norm_character, hd, ArchimedeanLocal.detPower, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.add_re, Complex.sub_re, hs]

/-- On the common positive chamber each pair of real parts controls the
double kernel by a continuous function of the square Schwartz test. -/
def ComplexLocalEqualProductTraceStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) (μ : Measure G) [μ.IsHaarMeasure]
    (a : ℂˣ) (ds es : List ComplexCharacterData)
    (U : complexWhittakerModel r ds a) (V : complexWhittakerModel (r + 1) es (-a)),
  ∃ (T σ : ℝ), ∀ (d₀ : ComplexCharacterData) (s₀ : ℂ), T ≤ d₀.exponent.re → σ < s₀.re →
    ∃ weight : 𝓢(Mat, ℂ) → ℝ, Continuous weight ∧ weight 0 = 0 ∧
      ∀ (Φ : 𝓢(Mat, ℂ)) (d : ComplexCharacterData) (s : ℂ),
        d.exponent.re = d₀.exponent.re → s.re = s₀.re →
        Integrable (complexEqualUnfoldedKernel d Φ U.val V.val s) (D.measure.prod μ) ∧
        (∫ p, ‖complexEqualUnfoldedKernel d Φ U.val V.val s p‖ ∂D.measure.prod μ) ≤ weight Φ

set_option maxHeartbeats 1600000 in
theorem complexLocalEqualProductTrace : ComplexLocalEqualProductTraceStatement (r := r) := by
  intro D μ _ a ds es U V
  let : SecondCountableTopology G := Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  let : SigmaFinite μ := inferInstance
  let : SigmaCompactSpace Q := (quotientHomeomorph m).isClosedEmbedding.sigmaCompactSpace
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  let : SigmaFinite D.measure := inferInstance
  obtain ⟨c, L, hI⟩ := complexLocalIwasawaProductMeasure (r := r) D
  obtain ⟨B, hB, σ, hExp⟩ := exists_equalProductBounds L a ds es U V
  refine ⟨((n : ℝ) + B) / 2, σ, fun d s hd hs => ?_⟩
  obtain ⟨C, J, hC, hBound⟩ := hExp d s hs
  let p := d.exponent.re + ((n : ℝ) - B) / 2
  have hGe : ((n : ℕ) : ℝ) ≤ p := by simp only [p, Nat.cast_add, Nat.cast_one]; linarith
  obtain ⟨P₀, hP₀, hPzero, hP⟩ := exists_squarePositiveWeight_bound μ J p hGe
  let Z := ∫⁻ x, torusEnvelope (r := r) x
  have hZ : Z < ⊤ := by
    simpa only [Z, torusEnvelope, neg_one_mul] using
      (@RealConvergenceAnalysis.lintegral_exp_neg_mul_sum_abs_lt_top m 1 one_pos)
  let R := (c : ℝ≥0∞) * Z * ENNReal.ofReal C
  have hR : R < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hZ) ENNReal.ofReal_lt_top
  refine ⟨fun Φ => R.toReal * P₀ Φ, hP₀.const_mul _, by simp [hPzero],
    fun Φ d' s' hd' hs' => ?_⟩
  let b (g : G) := max 1 ‖g.val‖ ^ J * ‖Φ g.val‖ * complexNormalizedAbs g.val.det ^ p
  have hBi : Integrable b μ := complexLocalSquarePositiveWeight μ Φ J p hGe
  have hb (g : G) : 0 ≤ b g := mul_nonneg (by positivity) (Real.rpow_nonneg (sq_nonneg _) _)
  let F := complexEqualUnfoldedKernel d Φ U.val V.val s
  have hF : Continuous F := continuous_complexEqualUnfoldedKernel U V d Φ s
  have hG (g : G) : (∫⁻ q, ENNReal.ofReal ‖F (q, g)‖ ∂D.measure) ≤ R * ENNReal.ofReal (b g) := by
    have hα : Continuous (fun k : K => equalProductAlpha k g) :=
      continuous_alpha.comp (((UnequalAnalytic.continuous_padGL (R := ℂ) (Nat.le_succ m)).comp
        continuous_subtype_val).mul continuous_const)
    have hδ : Continuous (fun k : K => equalTorusShift (equalProductAlpha k g)) :=
      continuous_pi fun i => ((continuous_apply i.castSucc).comp hα).sub
        ((continuous_apply (Fin.last m)).comp hα)
    refine (quotient_lintegral_le_shifted D c L hI (fun q => F (q, g))
      (hF.comp (continuous_id.prodMk continuous_const)) (C * b g) (mul_nonneg hC (hb g))
      (fun k => equalTorusShift (equalProductAlpha k g)) hδ.measurable ?_).trans_eq ?_
    · intro x k
      change Real.exp (L x) * ‖complexEqualUnfoldedKernel d Φ U.val V.val s
        (Quotient.mk _ (logTorus x * k.val), g)‖ ≤ _
      rw [complexEqualUnfoldedKernel, unfoldedInner_mk U V]
      exact (hBound Φ x k g).trans_eq (by dsimp only [b, p]; ring)
    · rw [ENNReal.ofReal_mul hC]
      dsimp only [R, Z]
      ac_rfl
  have hBfinite := (hasFiniteIntegral_iff_ofReal (ae_of_all _ hb)).mp hBi.hasFiniteIntegral
  have hsize : (∫⁻ p, ENNReal.ofReal ‖F p‖ ∂D.measure.prod μ) ≤
      R * ∫⁻ g, ENNReal.ofReal (b g) ∂μ := by
    calc
      _ = ∫⁻ g, ∫⁻ q, ENNReal.ofReal ‖F (q, g)‖ ∂D.measure ∂μ :=
        lintegral_prod_symm' _ (ENNReal.measurable_ofReal.comp hF.norm.measurable)
      _ ≤ ∫⁻ g, R * ENNReal.ofReal (b g) ∂μ := lintegral_mono hG
      _ = _ := lintegral_const_mul'' _ (ENNReal.measurable_ofReal.comp_aemeasurable hBi.aemeasurable)
  have hFin : R * (∫⁻ g, ENNReal.ofReal (b g) ∂μ) < ⊤ := ENNReal.mul_lt_top hR hBfinite
  let F' := complexEqualUnfoldedKernel d' Φ U.val V.val s'
  have hFn : Continuous F' := continuous_complexEqualUnfoldedKernel U V d' Φ s'
  have hNorm : (fun q => ‖F' q‖) = fun q => ‖F q‖ :=
    funext (norm_complexEqualUnfoldedKernel_of_re d' d hd' Φ U.val V.val s' s hs')
  refine ⟨⟨hFn.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_norm]
    change (∫⁻ q, ENNReal.ofReal ‖F' q‖ ∂D.measure.prod μ) < ⊤
    simp_rw [congrFun hNorm]
    exact hsize.trans_lt hFin
  · change (∫ q, ‖F' q‖ ∂D.measure.prod μ) ≤ R.toReal * P₀ Φ
    rw [hNorm, integral_eq_lintegral_of_nonneg_ae (.of_forall fun _ => norm_nonneg _)
      hF.norm.aestronglyMeasurable]
    refine (ENNReal.toReal_mono hFin.ne hsize).trans ?_
    rw [ENNReal.toReal_mul, ← integral_eq_lintegral_of_nonneg_ae (.of_forall hb) hBi.aestronglyMeasurable]
    exact mul_le_mul_of_nonneg_left (hP Φ) ENNReal.toReal_nonneg

/-- The full double kernel is absolutely integrable when the adjoining radial
exponent and the spectral real part exceed two independent thresholds. -/
def ComplexLocalEqualProductConvergenceStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) (μ : Measure G) [μ.IsHaarMeasure]
    (a : ℂˣ) (ds es : List ComplexCharacterData)
    (U : complexWhittakerModel r ds a) (V : complexWhittakerModel (r + 1) es (-a)),
  ∃ (T σ : ℝ), ∀ (d : ComplexCharacterData), T ≤ d.exponent.re →
    ∀ (Φ : 𝓢(Mat, ℂ)) (s : ℂ), σ < s.re →
      Integrable (complexEqualUnfoldedKernel d Φ U.val V.val s) (D.measure.prod μ)

theorem complexLocalEqualProductConvergence : ComplexLocalEqualProductConvergenceStatement (r := r) := by
  intro D μ _ a ds es U V
  obtain ⟨T, σ, h⟩ := complexLocalEqualProductTrace D μ a ds es U V
  refine ⟨T, σ, fun d hd Φ s hs => ?_⟩
  obtain ⟨_, _, _, hP⟩ := h d s hd hs
  exact (hP Φ d s rfl rfl).1

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
