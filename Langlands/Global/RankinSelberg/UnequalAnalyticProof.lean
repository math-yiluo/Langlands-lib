import Langlands.Global.RankinSelberg.UnequalAnalyticStatement
import Langlands.Global.RankinSelberg.UnequalAnalyticHolomorphy
import Langlands.Global.RankinSelberg.UnequalAnalyticIntegrability

/-! # Proof of the global analytic theory for unequal-rank cuspidal pairs

Proof of `Langlands.Global.RankinSelbergGlobal.UnequalAnalyticStatement` (Cogdell 2004,
Theorem 2.1, analytic and functional-equation clauses). The main work is `analytic_main`,
stated for abstract functions `φ` on `GL_(r+1)(𝔸)` and `φ'` on `GL_(t+1)(𝔸)`. It assumes that
both are continuous and left invariant under rational points, that `φ` decays rapidly on
matrices with a standard basis column and row (`HasBasisDecay`), and that `|φ'|` has finite
weighted integrals over `GL_(t+1)(F) \ GL_(t+1)(𝔸)`. The theorem
`unequalAnalyticStatement_proof` supplies these hypotheses for cusp forms
(`UnequalAnalyticDecay`, `UnequalAnalyticIntegrability`). -/

noncomputable section
universe u
set_option autoImplicit false

open NumberField MeasureTheory Langlands Langlands.Global Langlands.Automorphic
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Global.RankinSelbergGlobal.UnequalAnalytic

local instance proofSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance proofSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F]

local notation "R" => AdelicGroupPoints.rational F

/-- **The analytic theory for abstract automorphic data.** -/
theorem analytic_main {r t : ℕ} (h : t < r) (ψ : AddChar (Adeles F) ℂ) (hψc : Continuous ψ)
    (hψF : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) (hψ1 : ∀ x : Adeles F, ‖ψ x‖ = 1)
    (φ : Points F (r + 1) → ℂ) (hφc : Continuous φ)
    (hφr : ∀ (c : RationalGroupPoints F (Scheme F (r + 1))) (x : Points F (r + 1)),
      φ (R (Scheme F (r + 1)) c * x) = φ x)
    (hφP : HasBasisDecay F (r + 1) φ)
    (φ' : Points F (t + 1) → ℂ) (hφ'c : Continuous φ')
    (hφ'r : ∀ (c : RationalGroupPoints F (Scheme F (t + 1))) (x : Points F (t + 1)),
      φ' (R (Scheme F (t + 1)) c * x) = φ' x)
    (hφ'I : ∃ B₀ : ℝ, ∀ B : ℝ, B₀ ≤ B →
      ∫⁻ q, ‖φ' (Quotient.out q)‖ₑ *
          ENNReal.ofReal (Real.exp (-(B * |Real.log (detNorm F (t + 1) (Quotient.out q))|)))
        ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (t + 1)) < ⊤) :
    (∀ s : ℂ, Integrable (unequalIntegrand F h ψ φ φ' s)
      (AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (t + 1)))) ∧
    (∀ s : ℂ, Integrable (dualUnequalIntegrand F h ψ (dualFunction F (r + 1) φ)
      (dualFunction F (t + 1) φ') s)
      (AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (t + 1)))) ∧
    Differentiable ℂ (unequalIntegral F h ψ φ φ') ∧
    BoundedInVerticalStrips (unequalIntegral F h ψ φ φ') ∧
    ∀ s : ℂ, unequalIntegral F h ψ φ φ' s =
      dualUnequalIntegral F h ψ (dualFunction F (r + 1) φ) (dualFunction F (t + 1) φ') (1 - s) := by
  set μbar := AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (t + 1)) with hμbar
  let Γ := AdelicGroupPoints.rationalSubgroup F (Scheme F (t + 1))
  have hm : t + 1 < r + 1 := Nat.succ_lt_succ h
  /- The padded projection and the descended functions. -/
  let P : Points F (t + 1) → ℂ := fun g => projection F hm ψ φ (pad F (Nat.le_succ (t + 1)) g)
  have hPc : Continuous P := continuous_projection_pad hm hφc hφr hψF hψc hψ1 hφP
  have hPr : ∀ (c : RationalGroupPoints F (Scheme F (t + 1))) (g : Points F (t + 1)),
      P (R (Scheme F (t + 1)) c * g) = P g := fun c g =>
    projection_pad_rational_mul hm hφr hψF c g
  let Ag : Points F (t + 1) → ℂ := fun g => P g * φ' g
  have hAg : ∀ (c : Γ) (g : Points F (t + 1)), Ag ((c : Points F (t + 1)) * g) = Ag g := by
    rintro ⟨_, c, rfl⟩ g
    show P (R (Scheme F (t + 1)) c * g) * φ' (R (Scheme F (t + 1)) c * g) = P g * φ' g
    rw [hPr, hφ'r]
  let Lg : Points F (t + 1) → ℝ := fun g => Real.log (detNorm F (t + 1) g)
  have hLg : ∀ (c : Γ) (g : Points F (t + 1)), Lg ((c : Points F (t + 1)) * g) = Lg g := by
    rintro ⟨_, c, rfl⟩ g
    show Real.log (detNorm F (t + 1) (R (Scheme F (t + 1)) c * g)) =
      Real.log (detNorm F (t + 1) g)
    rw [detNorm_rational_mul]
  let A := LeftCosetSpace.lift Γ Ag hAg
  let L := LeftCosetSpace.lift Γ Lg hLg
  have hAc : Continuous A := LeftCosetSpace.continuous_lift Γ Ag hAg (hPc.mul hφ'c)
  have hLc : Continuous L := LeftCosetSpace.continuous_lift Γ Lg hLg
    ((continuous_detNorm F (t + 1)).log fun g => (detNorm_pos F g).ne')
  have hA : AEStronglyMeasurable A μbar := hAc.aestronglyMeasurable
  have hL : AEStronglyMeasurable L μbar := hLc.aestronglyMeasurable
  /- The integrand is `A exp ((s - 1/2) L)`. -/
  have hI : ∀ (s : ℂ) (q : AdelicGroupPoints.RationalQuotient F (Scheme F (t + 1))),
      unequalIntegrand F h ψ φ φ' s q = A q * Complex.exp ((s - 1 / 2) * (L q : ℂ)) := by
    intro s q
    simp only [A, L, lift_eq_out]
    rfl
  /- Exponential moments of `A`. -/
  have hint : ∀ σ : ℝ, Integrable (fun q => ‖A q‖ * Real.exp (σ * L q)) μbar := by
    intro σ
    obtain ⟨B₀, hB₀⟩ := hφ'I
    set B := max B₀ 0 with hB
    obtain ⟨C, hC0, hC⟩ := exists_norm_projection_pad_le hm hψ1 hφP (B + |σ|) (by positivity)
    refine integrable_of_enorm_le
      ((continuous_norm.comp hAc).mul (Real.continuous_exp.comp
        (continuous_const.mul hLc))).aestronglyMeasurable
      (hB₀ B (le_max_left _ _)) C (fun q => ?_)
    simp only [A, L, lift_eq_out]
    set g := Quotient.out q
    rw [Real.enorm_eq_ofReal (by positivity), ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
      ← ENNReal.ofReal_mul hC0]
    apply ENNReal.ofReal_le_ofReal
    have hPg : ‖P g‖ ≤ C * Real.exp (-((B + |σ|) * |Lg g|)) := hC g
    have hσ : σ * Lg g - (B + |σ|) * |Lg g| ≤ -(B * |Lg g|) := by
      have h1 := le_abs_self (σ * Lg g)
      rw [abs_mul] at h1
      linarith
    calc ‖Ag g‖ * Real.exp (σ * Lg g) = ‖P g‖ * ‖φ' g‖ * Real.exp (σ * Lg g) := by
          rw [norm_mul]
      _ ≤ C * Real.exp (-((B + |σ|) * |Lg g|)) * ‖φ' g‖ * Real.exp (σ * Lg g) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPg (norm_nonneg _))
            (Real.exp_pos _).le
      _ = C * (‖φ' g‖ * Real.exp (σ * Lg g - (B + |σ|) * |Lg g|)) := by
          rw [sub_eq_add_neg, Real.exp_add]
          ring
      _ ≤ C * (‖φ' g‖ * Real.exp (-(B * |Lg g|))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hσ)
            (norm_nonneg _)) hC0
  /- The integral is `J (s - 1/2)` with `J s = ∫ A exp (s L)`. -/
  have hJ : ∀ s : ℂ, unequalIntegral F h ψ φ φ' s =
      ∫ q, A q * Complex.exp ((s - 1 / 2) * (L q : ℂ)) ∂μbar := by
    intro s
    unfold unequalIntegral
    congr 1
    funext q
    exact hI s q
  /- Transpose inverse on the quotient preserves the measure. -/
  have hΓ := AdelicGroupPoints.isDiscrete_rationalSubgroup F (Scheme F (t + 1))
  let α := iotaEquiv F (t + 1)
  have hαΓ : ∀ x, α.toMulEquiv x ∈ Γ ↔ x ∈ Γ := by
    intro x
    change iota F (t + 1) x ∈ Γ ↔ x ∈ Γ
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨_, (iota_rational F c).symm.trans (by rw [hc, iota_iota])⟩
    · rintro ⟨c, hc⟩
      exact ⟨_, (iota_rational F c).symm.trans (by rw [hc])⟩
  have hm1 : Measurable α.toMulEquiv := α.continuous.measurable
  have hm2 : Measurable α.toMulEquiv.symm := α.symm.continuous.measurable
  let jq := cosetMeasurableEquiv Γ α.toMulEquiv hαΓ hm1 hm2
  have hmap : Measure.map jq μbar = μbar := by
    have h1 : Measure.map jq μbar = ((mulEquivHaarChar α : ℝ≥0∞))⁻¹ • μbar :=
      map_cosetMap_discreteQuotientMeasure Γ hΓ α.toMulEquiv hαΓ hm1 hm2 Measure.haar _
        (map_haar_eq_smul α)
    rw [Langlands.RankinSelberg.TwoBlockFirstBlockLaurent.mulEquivHaarChar_eq_one_of_involutive α (fun x => iota_iota F x), ENNReal.coe_one,
      inv_one, one_smul] at h1
    exact h1
  have hmp : MeasurePreserving jq μbar μbar := ⟨jq.measurable, hmap⟩
  have hjq : ∀ q, jq q = LeftCosetSpace.mk Γ (iota F (t + 1) (Quotient.out q)) := by
    intro q
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  /- The dual integrand is `A exp ((1/2 - s) L)` composed with transpose inverse. -/
  have hfun : (fun x => dualFunction F (r + 1) φ (iota F (r + 1) x)) = φ :=
    funext fun x => dualFunction_iota F φ hφr x
  have hD : ∀ (s : ℂ) (q : AdelicGroupPoints.RationalQuotient F (Scheme F (t + 1))),
      dualUnequalIntegrand F h ψ (dualFunction F (r + 1) φ) (dualFunction F (t + 1) φ') s q =
        A (jq q) * Complex.exp ((1 / 2 - s) * (L (jq q) : ℂ)) := by
    intro s q
    rw [hjq]
    simp only [A, L, LeftCosetSpace.lift_mk]
    set g := Quotient.out q
    show dualProjection F hm ψ (dualFunction F (r + 1) φ) (pad F (Nat.le_succ (t + 1)) g) *
        dualFunction F (t + 1) φ' g * detPower F (t + 1) g (s - 1 / 2) =
      P (iota F (t + 1) g) * φ' (iota F (t + 1) g) *
        Complex.exp ((1 / 2 - s) * (Real.log (detNorm F (t + 1) (iota F (t + 1) g)) : ℂ))
    rw [dualProjection, hfun, iota_pad, dualFunction_eq F φ' hφ'r, detNorm_iota, Real.log_inv,
      detPower]
    congr 2
    push_cast
    ring
  refine ⟨fun s => ?_, fun s => ?_, ?_, ?_, fun s => ?_⟩
  · -- integrability
    rw [show unequalIntegrand F h ψ φ φ' s = fun q => A q * Complex.exp ((s - 1 / 2) * (L q : ℂ))
      from funext (hI s)]
    exact integrable_mul_cexp hA hL hint (s - 1 / 2)
  · -- integrability of the dual integrand
    have hG := integrable_mul_cexp hA hL hint (1 / 2 - s)
    have hcomp := (hmp.integrable_comp_emb jq.measurableEmbedding).2 hG
    refine hcomp.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Function.comp_apply]
    exact (hD s q).symm
  · -- entire
    have hdiff := differentiable_integral_mul_cexp hA hL hint
    have he : unequalIntegral F h ψ φ φ' =
        (fun s : ℂ => ∫ q, A q * Complex.exp (s * (L q : ℂ)) ∂μbar) ∘ fun s => s - 1 / 2 :=
      funext fun s => hJ s
    rw [he]
    exact hdiff.comp (differentiable_id.sub_const _)
  · -- bounded in vertical strips
    intro a b _
    obtain ⟨C, hC0, hC⟩ := exists_norm_integral_mul_cexp_le hint (a - 1 / 2) (b - 1 / 2)
    refine ⟨C, hC0, fun s ha hb => ?_⟩
    rw [hJ s]
    have hre : (s - 1 / 2).re = s.re - 1 / 2 := by
      rw [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    exact hC (s - 1 / 2) (by rw [hre]; linarith) (by rw [hre]; linarith)
  · -- functional equation
    calc unequalIntegral F h ψ φ φ' s
        = ∫ q, A q * Complex.exp ((s - 1 / 2) * (L q : ℂ)) ∂μbar := hJ s
      _ = ∫ q, A (jq q) * Complex.exp ((s - 1 / 2) * (L (jq q) : ℂ)) ∂μbar :=
          (hmp.integral_comp' (fun q' => A q' * Complex.exp ((s - 1 / 2) * (L q' : ℂ)))).symm
      _ = dualUnequalIntegral F h ψ (dualFunction F (r + 1) φ) (dualFunction F (t + 1) φ')
            (1 - s) := by
          unfold dualUnequalIntegral
          congr 1
          funext q
          rw [hD, show (1 / 2 - (1 - s) : ℂ) = s - 1 / 2 by ring]

/-! ### Cusp forms -/

section Cusp

variable (F) [CompactSpace (AdeleQuotient F)]

local notation "e" => GeneralLinearGroupPoints.adelicHomeomorph F

theorem cuspFunction_eq {r : ℕ} (T : CuspidalOperatorRealization F r) (v : T.Space) :
    cuspFunction F T v = fun x => ContinuousRationalFunctions.evaluate F (r + 1)
      (T.realization.toContinuous v) (e (r + 1) x) := by
  funext x
  have hx := GroupSchemeFunctions.evaluate_continuousGeneralLinearEquiv_at_point F (r + 1)
    ((GroupSchemeFunctions.continuousGeneralLinearEquiv F (r + 1)).symm
      (T.realization.toContinuous v)) x
  rw [LinearEquiv.apply_symm_apply] at hx
  exact hx.symm

theorem continuous_cuspFunction {r : ℕ} (T : CuspidalOperatorRealization F r) (v : T.Space) :
    Continuous (cuspFunction F T v) := by
  rw [cuspFunction_eq]
  exact (ContinuousRationalFunctions.continuous_evaluate F (r + 1) _).comp
    (e (r + 1)).continuous

theorem cuspFunction_rational_mul {r : ℕ} (T : CuspidalOperatorRealization F r) (v : T.Space)
    (c : RationalGroupPoints F (Scheme F (r + 1))) (x : Points F (r + 1)) :
    cuspFunction F T v (R (Scheme F (r + 1)) c * x) = cuspFunction F T v x := by
  have h1 : e (r + 1) (R (Scheme F (r + 1)) c * x) =
      AdelicGL.rational F (r + 1) (GeneralLinearGroupPoints.rationalEquiv F (r + 1) c) *
        e (r + 1) x := by
    rw [map_mul, GeneralLinearGroupPoints.adelicHomeomorph_rational F (r + 1) c]
  rw [cuspFunction_eq]
  show ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous v)
      (e (r + 1) (R (Scheme F (r + 1)) c * x)) =
    ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous v) (e (r + 1) x)
  rw [h1]
  exact ContinuousRationalFunctions.evaluate_rational F (r + 1) _ _ _

theorem hasBasisDecay_cuspFunction {r : ℕ} (T : CuspidalOperatorRealization F r)
    (v : T.Space) : HasBasisDecay F (r + 1) (cuspFunction F T v) := by
  intro N hN
  obtain ⟨C, hC⟩ := exists_norm_le_of_basis_column_row T.realization T.cuspidal v
    (Nat.succ_pos r) N hN
  refine ⟨C, fun x hcol hrow => ?_⟩
  rw [cuspFunction_eq]
  exact hC (e (r + 1) x) hcol hrow

end Cusp

/-- **Cogdell 2004, Theorem 2.1 (analytic and functional-equation clauses).** -/
theorem unequalAnalyticStatement_proof : UnequalAnalyticStatement.{u} := by
  intro F _ _ _ r t h T T' ψ hψ v v'
  obtain ⟨hψc, -, hψF, hψ1⟩ := hψ
  have hI : ∃ B₀ : ℝ, ∀ B : ℝ, B₀ ≤ B →
      ∫⁻ q, ‖cuspFunction F T' v' (Quotient.out q)‖ₑ *
          ENNReal.ofReal (Real.exp (-(B * |Real.log (detNorm F (t + 1) (Quotient.out q))|)))
        ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (t + 1)) < ⊤ := by
    obtain ⟨B₀, hB₀⟩ := exists_lintegral_quotient_lt_top F T'.realization T'.cuspidal v'
    refine ⟨B₀, fun B hB => ?_⟩
    rw [cuspFunction_eq]
    exact hB₀ B hB
  exact analytic_main h ψ hψc hψF hψ1 _ (continuous_cuspFunction F T v)
    (cuspFunction_rational_mul F T v) (hasBasisDecay_cuspFunction F T v) _
    (continuous_cuspFunction F T' v') (cuspFunction_rational_mul F T' v') hI

end Langlands.Global.RankinSelbergGlobal.UnequalAnalytic
