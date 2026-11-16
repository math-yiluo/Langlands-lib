import Langlands.Representation.Archimedean.ComplexBlockParabolicSlices

/-!
# Proof of the integration formula along `P_{a,k}`

This module proves `ComplexBlockParabolicIntegrationStatement` as the theorem
`Langlands.Archimedean.complexBlockParabolicIntegration`, by induction on `k`, from the published
formula for `P_{m,1}` (`ComplexMaximalParabolicIntegration.integral_eq_chart`,
`ComplexJacquetLimit.integral_eq_chart'`). The formula for `P_{m,1}` is applied only to smooth
slices of the given function (`leviSlice`, `sliceT`).
-/

noncomputable section

open MeasureTheory Matrix

open scoped Matrix Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace ComplexBlockParabolicProof

open ComplexMaximalParabolicIntegration ComplexParabolicChartBound ComplexBlockParabolic
  ComplexBlockChart ComplexKIntegralInvariance Langlands.GeneralLinear ComplexPartialJacquet
  ComplexJacquetLimit ComplexDuality

/-- The integration formula for fixed `a, k`, without the integrability clause. -/
def BlockFormula (a k : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ F ∈ principalSeries ℂ (a + k) (ComplexKIntegralInvariance.modulusCharacter (a + k)),
      ∫ κ, F (κ : Langlands.GeneralLinear (a + k) ℂ) ∂unitaryHaar (a + k) =
        (c : ℂ) * ∫ κ₁ : unitaryCompact ℂ a, (∫ κ₂ : unitaryCompact ℂ k,
          (∫ X : Fin k → Fin a → ℂ,
            F (blockLowerGL (Matrix.of X) *
              blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (κ₂ : Langlands.GeneralLinear k ℂ)))
          ∂unitaryHaar k) ∂unitaryHaar a

/-! ## The integrability clause -/

theorem integrable_clause {a k : ℕ} {F : Langlands.GeneralLinear (a + k) ℂ → ℂ}
    (hF : F ∈ principalSeries ℂ (a + k) (modulusCharacter (a + k)))
    (κ₁ : unitaryCompact ℂ a) (κ₂ : unitaryCompact ℂ k) :
    Integrable fun X : Fin k → Fin a → ℂ =>
      F (blockLowerGL (Matrix.of X) *
        blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (κ₂ : Langlands.GeneralLinear k ℂ)) := by
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hF.1.continuous
  refine Integrable.mono' ((integrable_blockBound a k).const_mul C)
    ((hF.1.continuous.comp (ComplexBlockLimit.continuous_blockLowerGL.mul
      continuous_const)).aestronglyMeasurable) (ae_of_all _ fun X => ?_)
  exact norm_le_blockBound (normCov_of_mem hF) hC X
    (blockDiagGL_mem_unitaryCompact' κ₁.2 κ₂.2)

/-! ## The case `k = 0` -/

theorem blockDiagGL_zero {a : ℕ} (κ₁ : Langlands.GeneralLinear a ℂ)
    (κ₂ : Langlands.GeneralLinear 0 ℂ) : blockDiagGL κ₁ κ₂ = κ₁ := by
  apply Units.ext
  rw [ComplexBlockLimit.blockDiagGL_val]
  ext i j
  refine Fin.addCases (fun p => ?_) (fun q => q.elim0) i
  refine Fin.addCases (fun p' => ?_) (fun q => q.elim0) j
  simp only [ComplexBlockParabolic.blockDiag, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁]
  rfl

theorem blockFormula_zero (a : ℕ) : BlockFormula a 0 := by
  refine ⟨1, one_pos, fun F hF => ?_⟩
  have hX : ∀ (κ₁ : unitaryCompact ℂ a) (κ₂ : unitaryCompact ℂ 0),
      ∫ X : Fin 0 → Fin a → ℂ, F (blockLowerGL (Matrix.of X) *
        blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (κ₂ : Langlands.GeneralLinear 0 ℂ)) =
      F (κ₁ : Langlands.GeneralLinear a ℂ) := by
    intro κ₁ κ₂
    rw [integral_unique, blockLowerGL_zero_rows, one_mul, blockDiagGL_zero]
    have h1 : (volume : Measure (Fin 0 → Fin a → ℂ)).real Set.univ = 1 := by
      rw [measureReal_def, volume_pi, Measure.pi_univ]
      simp
    rw [h1, one_smul]
  simp_rw [hX, integral_const, probReal_univ, one_smul, Complex.ofReal_one, one_mul]
  rfl

/-! ## Determinants and continuity -/

section Points

variable {a k : ℕ}

theorem det_blockLowerGL (X : Matrix (Fin k) (Fin a) ℂ) :
    ((blockLowerGL X : Langlands.GeneralLinear (a + k) ℂ) :
      Matrix (Fin (a + k)) (Fin (a + k)) ℂ).det = 1 := by
  rw [blockLowerGL_val, det_blockLower]

theorem norm_det_point (X : Matrix (Fin k) (Fin a) ℂ) (κ₁ : unitaryCompact ℂ a)
    (τ : unitaryCompact ℂ k) :
    ‖((blockLowerGL X * blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ)
      (τ : Langlands.GeneralLinear k ℂ) : Langlands.GeneralLinear (a + k) ℂ) :
        Matrix (Fin (a + k)) (Fin (a + k)) ℂ).det‖ = 1 := by
  rw [Units.val_mul, Matrix.det_mul, det_blockLowerGL, one_mul, ComplexBlockLimit.blockDiagGL_val,
    det_blockDiag, norm_mul, normSq_det_unitary κ₁.2, normSq_det_unitary τ.2, one_mul]

theorem normSqC_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : normSqC z = 1 := by
  rw [normSqC, hz]
  simp

theorem norm_det_inv_of_norm_one {n : ℕ} {g : Langlands.GeneralLinear n ℂ}
    (hg : ‖(g : Matrix (Fin n) (Fin n) ℂ).det‖ = 1) :
    ‖((g⁻¹ : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ).det‖ = 1 := by
  rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_inv, hg, inv_one]

theorem continuous_point :
    Continuous fun p : unitaryCompact ℂ a × (unitaryCompact ℂ k × (Fin k → Fin a → ℂ)) =>
      blockLowerGL (a := a) (k := k) (Matrix.of p.2.2) *
        blockDiagGL (p.1 : Langlands.GeneralLinear a ℂ) (p.2.1 : Langlands.GeneralLinear k ℂ) :=
  (ComplexBlockLimit.continuous_blockLowerGL.comp (continuous_snd.comp continuous_snd)).mul
    (ComplexBlockLimit.continuous_blockDiagGL.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))))

end Points

/-! ## Integrals along `J(v, 1) ι(g)` -/

section ChartIota

variable {m : ℕ} {F : Langlands.GeneralLinear (m + 1) ℂ → ℂ}

theorem integrable_iota_chart (hF : NormCov (m + 1) F) (hc : Continuous F) {C : ℝ}
    (hC : ∀ κ ∈ unitaryCompact ℂ (m + 1), ‖F κ‖ ≤ C) (g : Langlands.GeneralLinear m ℂ) :
    Integrable fun v : Fin m → ℂ => F (iotaGL g * chartGL v) := by
  simp_rw [iotaGL_mul_chartGL]
  exact integrable_comp_vecMul (det_inv_ne_zero g) (integrable_chart_iota hF hc hC g)

theorem integral_norm_iota_chart {g : Langlands.GeneralLinear m ℂ}
    (hg : ‖(g : Matrix (Fin m) (Fin m) ℂ).det‖ = 1) :
    ∫ v : Fin m → ℂ, ‖F (iotaGL g * chartGL v)‖ = chartNorm F g := by
  simp_rw [iotaGL_mul_chartGL]
  rw [integral_vecMul_smul (det_inv_ne_zero g) (fun v => ‖F (chartGL v * iotaGL g)‖),
    norm_det_inv_of_norm_one hg, one_pow, inv_one, one_smul, chartNorm]

end ChartIota

/-! ## Step 1: the formula for `P_{a+k,1}`, then the formula for `P_{a,k}` on Levi slices -/

section StepOne

variable {a k : ℕ}

/-- The iterated integral
`Z(F) = ∫_{U(a)} ∫_{U(k)} ∫_{M_{k×a}} ∫_{ℂ^{a+k}} F(ι(n̄(X')) J(v, 1) ι(diag(κ₁, τ)))`. -/
def chartIntegral (F : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ) : ℂ :=
  ∫ κ₁ : unitaryCompact ℂ a, (∫ τ : unitaryCompact ℂ k, (∫ X' : Fin k → Fin a → ℂ,
    ∫ v : Fin (a + k) → ℂ, F (iotaGL (blockLowerGL (Matrix.of X')) * chartGL v *
      iotaGL (blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (τ : Langlands.GeneralLinear k ℂ))))
    ∂unitaryHaar k) ∂unitaryHaar a

theorem step_one_fubini {F : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}
    (hF : F ∈ principalSeries ℂ (a + (k + 1)) (modulusCharacter (a + (k + 1)))) :
    ∫ v : Fin (a + k) → ℂ, (∫ κ₁ : unitaryCompact ℂ a, (∫ τ : unitaryCompact ℂ k,
      (∫ X' : Fin k → Fin a → ℂ, F (iotaGL (blockLowerGL (Matrix.of X') *
        blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (τ : Langlands.GeneralLinear k ℂ)) *
          chartGL v)) ∂unitaryHaar k) ∂unitaryHaar a) = chartIntegral F := by
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hF.1.continuous
  have hcov : NormCov (a + (k + 1)) F := normCov_of_mem hF
  have hFc : Continuous F := hF.1.continuous
  set μΩ : Measure (unitaryCompact ℂ a × (unitaryCompact ℂ k × (Fin k → Fin a → ℂ))) :=
    (unitaryHaar a).prod ((unitaryHaar k).prod volume) with hμΩ
  set H : unitaryCompact ℂ a × (unitaryCompact ℂ k × (Fin k → Fin a → ℂ)) →
      (Fin (a + k) → ℂ) → ℂ := fun p v =>
    F (iotaGL (blockLowerGL (Matrix.of p.2.2) *
      blockDiagGL (p.1 : Langlands.GeneralLinear a ℂ) (p.2.1 : Langlands.GeneralLinear k ℂ)) *
        chartGL v) with hH
  set G : unitaryCompact ℂ a × (unitaryCompact ℂ k × (Fin k → Fin a → ℂ)) →
      (Fin (a + k) → ℂ) → ℂ := fun p v =>
    F (iotaGL (blockLowerGL (Matrix.of p.2.2)) * chartGL v *
      iotaGL (blockDiagGL (p.1 : Langlands.GeneralLinear a ℂ)
        (p.2.1 : Langlands.GeneralLinear k ℂ))) with hG
  have hHc : Continuous (Function.uncurry H) :=
    hFc.comp ((continuous_iotaGL.comp (continuous_point.comp continuous_fst)).mul
      (continuous_chartGL.comp continuous_snd))
  -- the chart norm along the points `n̄(X') diag(κ₁, τ)`
  have hCN : ∀ κ ∈ unitaryCompact ℂ (a + k), ‖((chartNorm F κ : ℝ) : ℂ)‖ ≤
      C * ∫ x : Fin (a + k) → ℂ, ∏ l : Fin (a + k), (1 + ‖x l‖ ^ 2) ^ (-2 : ℝ) := fun κ hκ => by
    rw [norm_chartNorm]
    exact chartNorm_le hcov hC hκ
  have hjoint : Integrable (Function.uncurry H) (μΩ.prod volume) := by
    rw [integrable_prod_iff hHc.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun p => ?_, ?_⟩
    · change Integrable (fun v => F (iotaGL (blockLowerGL (Matrix.of p.2.2) *
        blockDiagGL (p.1 : Langlands.GeneralLinear a ℂ) (p.2.1 : Langlands.GeneralLinear k ℂ)) *
          chartGL v)) volume
      exact integrable_iota_chart (m := a + k) hcov hFc hC _
    refine Integrable.mono' ((((integrable_blockBound a k).const_mul
      (C * ∫ x : Fin (a + k) → ℂ, ∏ l : Fin (a + k), (1 + ‖x l‖ ^ 2) ^ (-2 : ℝ))).comp_snd
        (unitaryHaar k)).comp_snd (unitaryHaar a))
      hHc.aestronglyMeasurable.norm.integral_prod_right' (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    change ∫ v, ‖H p v‖ ≤ _
    simp only [hH]
    rw [integral_norm_iota_chart (norm_det_point _ p.1 p.2.1), ← norm_chartNorm]
    exact norm_le_blockBound (normCov_chartNorm hcov) hCN p.2.2
      (blockDiagGL_mem_unitaryCompact' p.1.2 p.2.1.2)
  have hsec : ∀ v : Fin (a + k) → ℂ, Integrable (fun p => H p v) μΩ := by
    intro v
    have hS := leviSlice_mem hF (chartGL v)
    obtain ⟨Cv, hCv⟩ := exists_bound_unitaryCompact hS.1.continuous
    refine Integrable.mono' ((((integrable_blockBound a k).const_mul Cv).comp_snd
      (unitaryHaar k)).comp_snd (unitaryHaar a))
      ((hHc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
      (ae_of_all _ fun p => ?_)
    have hb := norm_le_blockBound (normCov_of_mem hS) hCv p.2.2
      (blockDiagGL_mem_unitaryCompact' p.1.2 p.2.1.2)
    rw [leviSlice, normSqC_of_norm_one (norm_det_point _ p.1 p.2.1), inv_one, mul_one] at hb
    exact hb
  have hsub : ∀ p, ∫ v, H p v = ∫ v, G p v := by
    intro p
    simp only [hH, hG]
    set D : Langlands.GeneralLinear (a + k) ℂ :=
      blockDiagGL (p.1 : Langlands.GeneralLinear a ℂ) (p.2.1 : Langlands.GeneralLinear k ℂ) with hD
    have hD1 : ‖(D : Matrix (Fin (a + k)) (Fin (a + k)) ℂ).det‖ = 1 := by
      rw [hD, ComplexBlockLimit.blockDiagGL_val, det_blockDiag, norm_mul,
        normSq_det_unitary p.1.2, normSq_det_unitary p.2.1.2, one_mul]
    have h1 : ∀ v : Fin (a + k) → ℂ,
        F (iotaGL (blockLowerGL (Matrix.of p.2.2) * D) * chartGL v) =
          F (iotaGL (blockLowerGL (Matrix.of p.2.2)) *
            chartGL (v ᵥ* ((D⁻¹ : Langlands.GeneralLinear (a + k) ℂ) :
              Matrix (Fin (a + k)) (Fin (a + k)) ℂ)) * iotaGL D) := fun v => by
      rw [map_mul, mul_assoc, iotaGL_mul_chartGL, ← mul_assoc]
    simp_rw [h1]
    rw [integral_vecMul_eq (det_inv_ne_zero D)
      (fun v => F (iotaGL (blockLowerGL (Matrix.of p.2.2)) * chartGL v * iotaGL D)),
      norm_det_inv_of_norm_one hD1, one_pow, inv_one, Complex.ofReal_one, one_mul]
  have hintG : Integrable (fun p => ∫ v, G p v) μΩ :=
    hjoint.integral_prod_left.congr (ae_of_all _ hsub)
  calc ∫ v : Fin (a + k) → ℂ, (∫ κ₁ : unitaryCompact ℂ a, (∫ τ : unitaryCompact ℂ k,
        (∫ X' : Fin k → Fin a → ℂ, F (iotaGL (blockLowerGL (Matrix.of X') *
          blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (τ : Langlands.GeneralLinear k ℂ)) *
            chartGL v)) ∂unitaryHaar k) ∂unitaryHaar a)
      = ∫ v : Fin (a + k) → ℂ, ∫ p, H p v ∂μΩ :=
        integral_congr_ae (ae_of_all _ fun v => (integral_prod_prod (hsec v)).symm)
    _ = ∫ p, (∫ v, H p v) ∂μΩ := (integral_integral_swap hjoint).symm
    _ = ∫ p, (∫ v, G p v) ∂μΩ := integral_congr_ae (ae_of_all _ hsub)
    _ = chartIntegral F := integral_prod_prod hintG

/-- **Step 1.** `∫_{U(a+k+1)} F = c_{a+k} c₀ Z(F)`, where `c₀` is the constant of the formula for
`P_{a,k}`. -/
theorem step_one (hIH : BlockFormula a k) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ F ∈ principalSeries ℂ (a + (k + 1)) (modulusCharacter (a + (k + 1))),
      ∫ κ, F (κ : Langlands.GeneralLinear (a + (k + 1)) ℂ) ∂unitaryHaar (a + (k + 1)) =
        ((chartConstant (a + k) * c₀ : ℝ) : ℂ) * chartIntegral F := by
  obtain ⟨c₀, hc₀, hIH⟩ := hIH
  refine ⟨c₀, hc₀, fun F hF => ?_⟩
  have hnat : ∀ v : Fin (a + k) → ℂ, natural F (chartGL v) =
      (c₀ : ℂ) * ∫ κ₁ : unitaryCompact ℂ a, (∫ τ : unitaryCompact ℂ k,
        (∫ X' : Fin k → Fin a → ℂ, F (iotaGL (blockLowerGL (Matrix.of X') *
          blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (τ : Langlands.GeneralLinear k ℂ)) *
            chartGL v)) ∂unitaryHaar k) ∂unitaryHaar a := by
    intro v
    have h1 := hIH (leviSlice F (chartGL v)) (leviSlice_mem hF (chartGL v))
    have e1 : ∀ κ : unitaryCompact ℂ (a + k),
        leviSlice F (chartGL v) (κ : Langlands.GeneralLinear (a + k) ℂ) =
          F (iotaGL (κ : Langlands.GeneralLinear (a + k) ℂ) * chartGL v) := fun κ => by
      rw [leviSlice, normSqC_det_unitary, inv_one, mul_one]
      rfl
    have e2 : ∀ (κ₁ : unitaryCompact ℂ a) (τ : unitaryCompact ℂ k) (X' : Fin k → Fin a → ℂ),
        leviSlice F (chartGL v) (blockLowerGL (Matrix.of X') *
          blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (τ : Langlands.GeneralLinear k ℂ)) =
        F (iotaGL (blockLowerGL (Matrix.of X') *
          blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ) (τ : Langlands.GeneralLinear k ℂ)) *
            chartGL v) := fun κ₁ τ X' => by
      rw [leviSlice, normSqC_of_norm_one (norm_det_point _ κ₁ τ), inv_one, mul_one]
      rfl
    simp only [e1, e2] at h1
    exact h1
  refine (integral_eq_chart (m := a + k) hF).trans ?_
  simp_rw [hnat]
  rw [integral_const_mul, step_one_fubini hF]
  push_cast
  ring

end StepOne

/-! ## Step 2: slices along `GL_{k+1}(ℂ)` and the formula for `P_{k,1}` -/

section StepTwo

variable {a k : ℕ} {F : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}

theorem norm_det_chart_iota (w : Fin k → ℂ) (τ : unitaryCompact ℂ k) :
    ‖((chartGL w * iotaGL (τ : Langlands.GeneralLinear k ℂ) : Langlands.GeneralLinear (k + 1) ℂ) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ).det‖ = 1 := by
  rw [Units.val_mul, Matrix.det_mul, chartGL, JGL_val, det_Jmat, Fin.snoc_last, one_mul,
    iotaGL_val, det_iota, normSq_det_unitary τ.2]

theorem det_ne_zero_GL {n : ℕ} (g : Langlands.GeneralLinear n ℂ) :
    (g : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit g)).ne_zero

/-- The point `n̄(X) diag(κ₁, 1)` at which the slices along `GL_{k+1}(ℂ)` are taken. -/
def slicePoint (κ₁ : Langlands.GeneralLinear a ℂ) (X : Fin (k + 1) → Fin a → ℂ) :
    Langlands.GeneralLinear (a + (k + 1)) ℂ :=
  blockLowerGL (Matrix.of X) * blockDiagGL κ₁ 1

/-- `T_X(h) = F(n̄(h X) diag(κ₁, h)) |det h|^{2a}`. -/
theorem sliceT_point (κ₁ : Langlands.GeneralLinear a ℂ) (X : Fin (k + 1) → Fin a → ℂ)
    (h : Langlands.GeneralLinear (k + 1) ℂ) :
    sliceT F (slicePoint κ₁ X) h =
      F (blockLowerGL ((h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) * Matrix.of X) *
        blockDiagGL κ₁ h) * normSqC (h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ).det ^ a := by
  rw [sliceT, slicePoint, ← mul_assoc, blockDiagGL_mul_blockLowerGL]

/-- `∫_X T_X(h) dX = ∫_X F(n̄(X) diag(κ₁, h)) dX` when `|det h| = 1`. -/
theorem integral_sliceT_point (κ₁ : Langlands.GeneralLinear a ℂ)
    {h : Langlands.GeneralLinear (k + 1) ℂ}
    (hh : ‖(h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ).det‖ = 1) :
    ∫ X : Fin (k + 1) → Fin a → ℂ, sliceT F (slicePoint κ₁ X) h =
      ∫ X : Fin (k + 1) → Fin a → ℂ, F (blockLowerGL (Matrix.of X) * blockDiagGL κ₁ h) := by
  simp_rw [sliceT_point, normSqC_of_norm_one hh, one_pow, mul_one]
  have h2 : ∫ X : Fin (k + 1) → Fin a → ℂ,
      F (blockLowerGL ((h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) * Matrix.of X) *
        blockDiagGL κ₁ h) =
      ((((‖(h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ).det‖ ^ 2) ^ a)⁻¹ : ℝ) : ℂ) *
        ∫ X : Fin (k + 1) → Fin a → ℂ, F (blockLowerGL (Matrix.of X) * blockDiagGL κ₁ h) :=
    integral_leftMul_eq (det_ne_zero_GL h)
      (fun X => F (blockLowerGL (Matrix.of X) * blockDiagGL κ₁ h))
  rw [h2, hh, one_pow, one_pow, inv_one, Complex.ofReal_one, one_mul]

theorem integral_norm_sliceT_point (κ₁ : Langlands.GeneralLinear a ℂ)
    {h : Langlands.GeneralLinear (k + 1) ℂ}
    (hh : ‖(h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ).det‖ = 1) :
    ∫ X : Fin (k + 1) → Fin a → ℂ, ‖sliceT F (slicePoint κ₁ X) h‖ =
      blockNorm F κ₁ h := by
  simp_rw [sliceT_point, normSqC_of_norm_one hh, one_pow, mul_one]
  have h2 : ∫ X : Fin (k + 1) → Fin a → ℂ,
      ‖F (blockLowerGL ((h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) * Matrix.of X) *
        blockDiagGL κ₁ h)‖ =
      ((‖(h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ).det‖ ^ 2) ^ a)⁻¹ *
        ∫ X : Fin (k + 1) → Fin a → ℂ, ‖F (blockLowerGL (Matrix.of X) * blockDiagGL κ₁ h)‖ :=
    integral_leftMul_eq_real (det_ne_zero_GL h)
      (fun X => ‖F (blockLowerGL (Matrix.of X) * blockDiagGL κ₁ h)‖)
  rw [h2, hh, one_pow, one_pow, inv_one, one_mul, blockNorm]

theorem integrable_sliceT_point (hF : NormCov (a + (k + 1)) F) (hFc : Continuous F) {C : ℝ}
    (hC : ∀ κ ∈ unitaryCompact ℂ (a + (k + 1)), ‖F κ‖ ≤ C) {κ₁ : Langlands.GeneralLinear a ℂ}
    (hκ₁ : κ₁ ∈ unitaryCompact ℂ a) (h : Langlands.GeneralLinear (k + 1) ℂ) :
    Integrable fun X : Fin (k + 1) → Fin a → ℂ =>
      sliceT F (slicePoint κ₁ X) h := by
  simp_rw [sliceT_point]
  exact (integrable_comp_leftMul (det_ne_zero_GL h)
    (integrable_block_diag hF hFc hC hκ₁ h)).mul_const _

theorem continuous_sliceT_point (hFc : Continuous F) (κ₁ : Langlands.GeneralLinear a ℂ)
    {T : Type*} [TopologicalSpace T] {h : T → Langlands.GeneralLinear (k + 1) ℂ}
    {X : T → Fin (k + 1) → Fin a → ℂ} (hh : Continuous h) (hX : Continuous X) :
    Continuous fun t => sliceT F (slicePoint κ₁ (X t)) (h t) := by
  unfold sliceT slicePoint
  refine (hFc.comp ((ComplexBlockLimit.continuous_blockDiagGL.comp
    (continuous_const.prodMk hh)).mul
      ((ComplexBlockLimit.continuous_blockLowerGL.comp hX).mul
        continuous_const))).mul ?_
  exact (contMDiff_normSqC_det_pow a).continuous.comp hh

/-- **Step 2** for fixed `κ₁`. -/
theorem step_two_inner (hF : F ∈ principalSeries ℂ (a + (k + 1)) (modulusCharacter (a + (k + 1))))
    {κ₁ : Langlands.GeneralLinear a ℂ} (hκ₁ : κ₁ ∈ unitaryCompact ℂ a) :
    ∫ κ₂ : unitaryCompact ℂ (k + 1), (∫ X : Fin (k + 1) → Fin a → ℂ,
      F (blockLowerGL (Matrix.of X) * blockDiagGL κ₁
        (κ₂ : Langlands.GeneralLinear (k + 1) ℂ))) ∂unitaryHaar (k + 1) =
      (chartConstant k : ℂ) * ∫ τ : unitaryCompact ℂ k, (∫ X' : Fin k → Fin a → ℂ,
        ∫ v : Fin (a + k) → ℂ, F (iotaGL (blockLowerGL (Matrix.of X')) * chartGL v *
          iotaGL (blockDiagGL κ₁
            (τ : Langlands.GeneralLinear k ℂ)))) ∂unitaryHaar k := by
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hF.1.continuous
  have hcov : NormCov (a + (k + 1)) F := normCov_of_mem hF
  have hFc : Continuous F := hF.1.continuous
  set C₂ : ℝ := C * ∫ X, blockBound a (k + 1) X with hC₂
  have hCB : ∀ κ ∈ unitaryCompact ℂ (k + 1),
      ‖((blockNorm F κ₁ κ : ℝ) : ℂ)‖ ≤ C₂ := fun κ hκ => by
    rw [norm_blockNorm]
    exact blockNorm_le hcov hC hκ₁ hκ
  -- (a) the slices
  have h2a : ∀ κ₂ : unitaryCompact ℂ (k + 1),
      ∫ X : Fin (k + 1) → Fin a → ℂ, F (blockLowerGL (Matrix.of X) *
        blockDiagGL κ₁ (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)) =
      ∫ X, sliceT F (slicePoint κ₁ X) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ) := fun κ₂ =>
    (integral_sliceT_point κ₁ (normSq_det_unitary κ₂.2)).symm
  -- (b) exchange of `κ₂` and `X`
  have hjoint2 : Integrable (Function.uncurry fun (κ₂ : unitaryCompact ℂ (k + 1))
      (X : Fin (k + 1) → Fin a → ℂ) =>
        sliceT F (slicePoint κ₁ X) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ))
      ((unitaryHaar (k + 1)).prod volume) := by
    refine integrable_prod_of_bounded
      ((continuous_sliceT_point hFc κ₁
        (continuous_subtype_val.comp continuous_fst) continuous_snd).aestronglyMeasurable)
      (fun κ₂ => by
        change Integrable (fun X : Fin (k + 1) → Fin a → ℂ =>
          sliceT F (slicePoint κ₁ X)
            (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)) volume
        exact integrable_sliceT_point (k := k) hcov hFc hC hκ₁ _) (M := C₂) fun κ₂ => ?_
    change ∫ X, ‖sliceT F (slicePoint κ₁ X) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)‖ ≤ C₂
    rw [integral_norm_sliceT_point _ (normSq_det_unitary κ₂.2), ← norm_blockNorm]
    exact hCB _ κ₂.2
  -- (c), (d) the formula for `P_{k,1}` on each slice, flattened
  set μq : Measure (unitaryCompact ℂ k × (Fin k → ℂ)) := (unitaryHaar k).prod volume with hμq
  have h2c : ∀ X : Fin (k + 1) → Fin a → ℂ,
      ∫ κ₂ : unitaryCompact ℂ (k + 1),
        sliceT F (slicePoint κ₁ X) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)
        ∂unitaryHaar (k + 1) =
      (chartConstant k : ℂ) * ∫ q, sliceT F (slicePoint κ₁ X) (chartGL q.2 * iotaGL
        (q.1 : Langlands.GeneralLinear k ℂ)) ∂μq := by
    intro X
    have hS := sliceT_mem hF (slicePoint κ₁ X)
    obtain ⟨CX, hCX⟩ := exists_bound_unitaryCompact hS.1.continuous
    rw [integral_eq_chart' (m := k) hS]
    congr 1
    refine (integral_prod (μ := unitaryHaar k) (ν := (volume : Measure (Fin k → ℂ)))
      (fun q : unitaryCompact ℂ k × (Fin k → ℂ) => sliceT F (slicePoint κ₁ X)
        (chartGL q.2 * iotaGL (q.1 : Langlands.GeneralLinear k ℂ))) ?_).symm
    refine Integrable.mono' ((integrable_chartBound.const_mul CX).comp_snd (unitaryHaar k))
      ((hS.1.continuous.comp ((continuous_chartGL.comp continuous_snd).mul
        (continuous_iotaGL.comp
          (continuous_subtype_val.comp continuous_fst)))).aestronglyMeasurable)
      (ae_of_all _ fun q => ?_)
    exact norm_le_chartBound (normCov_of_mem hS) hCX q.2 (iotaGL_mem_unitaryCompact q.1.2)
  -- (e) exchange of `X` and `(τ, w)`
  have hcont3 : Continuous (Function.uncurry fun (q : unitaryCompact ℂ k × (Fin k → ℂ))
      (X : Fin (k + 1) → Fin a → ℂ) =>
        sliceT F (slicePoint κ₁ X)
          (chartGL q.2 * iotaGL (q.1 : Langlands.GeneralLinear k ℂ))) :=
    continuous_sliceT_point hFc κ₁
      (h := fun p : (unitaryCompact ℂ k × (Fin k → ℂ)) × (Fin (k + 1) → Fin a → ℂ) =>
        chartGL p.1.2 * iotaGL (p.1.1 : Langlands.GeneralLinear k ℂ))
      ((continuous_chartGL.comp (continuous_snd.comp continuous_fst)).mul
        (continuous_iotaGL.comp (continuous_subtype_val.comp
          (continuous_fst.comp continuous_fst)))) continuous_snd
  have hjoint3 : Integrable (Function.uncurry fun (q : unitaryCompact ℂ k × (Fin k → ℂ))
      (X : Fin (k + 1) → Fin a → ℂ) =>
        sliceT F (slicePoint κ₁ X) (chartGL q.2 * iotaGL (q.1 : Langlands.GeneralLinear k ℂ)))
      (μq.prod volume) := by
    rw [integrable_prod_iff hcont3.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun q => ?_, ?_⟩
    · change Integrable (fun X : Fin (k + 1) → Fin a → ℂ =>
        sliceT F (slicePoint κ₁ X)
          (chartGL q.2 * iotaGL (q.1 : Langlands.GeneralLinear k ℂ))) volume
      exact integrable_sliceT_point (k := k) hcov hFc hC hκ₁ _
    refine Integrable.mono' ((integrable_chartBound.const_mul C₂).comp_snd (unitaryHaar k))
      hcont3.aestronglyMeasurable.norm.integral_prod_right' (ae_of_all _ fun q => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    change ∫ X, ‖sliceT F (slicePoint κ₁ X)
      (chartGL q.2 * iotaGL (q.1 : Langlands.GeneralLinear k ℂ))‖ ≤ _
    rw [integral_norm_sliceT_point _ (norm_det_chart_iota q.2 q.1), ← norm_blockNorm]
    exact norm_le_chartBound (normCov_blockNorm hcov _) hCB q.2 (iotaGL_mem_unitaryCompact q.1.2)
  -- (f), (g)
  have h2f : ∀ q : unitaryCompact ℂ k × (Fin k → ℂ),
      ∫ X, sliceT F (slicePoint κ₁ X) (chartGL q.2 * iotaGL (q.1 : Langlands.GeneralLinear k ℂ)) =
      ∫ X : Fin (k + 1) → Fin a → ℂ, F (blockLowerGL (Matrix.of X) *
        blockDiagGL κ₁
          (chartGL q.2 * iotaGL (q.1 : Langlands.GeneralLinear k ℂ))) := fun q =>
    integral_sliceT_point _ (norm_det_chart_iota q.2 q.1)
  have hint3 : Integrable (fun q : unitaryCompact ℂ k × (Fin k → ℂ) =>
      ∫ X : Fin (k + 1) → Fin a → ℂ, F (blockLowerGL (Matrix.of X) *
        blockDiagGL κ₁
          (chartGL q.2 * iotaGL (q.1 : Langlands.GeneralLinear k ℂ)))) μq :=
    hjoint3.integral_prod_left.congr (ae_of_all _ h2f)
  -- (h) the rearrangement, for fixed `τ`
  have h2h : ∀ τ : unitaryCompact ℂ k,
      ∫ w : Fin k → ℂ, ∫ X : Fin (k + 1) → Fin a → ℂ, F (blockLowerGL (Matrix.of X) *
        blockDiagGL κ₁
          (chartGL w * iotaGL (τ : Langlands.GeneralLinear k ℂ))) =
      ∫ X' : Fin k → Fin a → ℂ, ∫ v : Fin (a + k) → ℂ,
        F (iotaGL (blockLowerGL (Matrix.of X')) * chartGL v *
          iotaGL (blockDiagGL κ₁
            (τ : Langlands.GeneralLinear k ℂ))) := by
    intro τ
    set f : (Fin k → ℂ) × (Fin (k + 1) → Fin a → ℂ) → ℂ := fun q =>
      F (blockLowerGL (Matrix.of q.2) * blockDiagGL κ₁
        (chartGL q.1 * iotaGL (τ : Langlands.GeneralLinear k ℂ))) with hfdef
    have hfc : Continuous f :=
      hFc.comp ((ComplexBlockLimit.continuous_blockLowerGL.comp continuous_snd).mul
        (ComplexBlockLimit.continuous_blockDiagGL.comp (continuous_const.prodMk
          ((continuous_chartGL.comp continuous_fst).mul continuous_const))))
    have hf : Integrable f ((volume : Measure (Fin k → ℂ)).prod volume) := by
      rw [integrable_prod_iff hfc.aestronglyMeasurable]
      refine ⟨ae_of_all _ fun w => ?_, ?_⟩
      · change Integrable (fun X : Fin (k + 1) → Fin a → ℂ => F (blockLowerGL (Matrix.of X) *
          blockDiagGL κ₁
            (chartGL w * iotaGL (τ : Langlands.GeneralLinear k ℂ)))) volume
        exact integrable_block_diag (k := k) hcov hFc hC hκ₁ _
      refine Integrable.mono' (integrable_chartBound.const_mul C₂)
        hfc.aestronglyMeasurable.norm.integral_prod_right' (ae_of_all _ fun w => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      change blockNorm F κ₁
        (chartGL w * iotaGL (τ : Langlands.GeneralLinear k ℂ)) ≤ _
      rw [← norm_blockNorm]
      exact norm_le_chartBound (normCov_blockNorm hcov _) hCB w (iotaGL_mem_unitaryCompact τ.2)
    have hfr : ∀ q : (Fin k → Fin a → ℂ) × (Fin (a + k) → ℂ), f (rowsChart a k q) =
        F (iotaGL (blockLowerGL (Matrix.of q.1)) * chartGL q.2 *
          iotaGL (blockDiagGL κ₁
            (τ : Langlands.GeneralLinear k ℂ))) := by
      rintro ⟨X', v⟩
      rw [rowsChart_apply]
      simp only [hfdef]
      rw [blockLowerGL_mul_blockDiagGL_chart, Fin.append_castAdd_natAdd]
    calc ∫ w : Fin k → ℂ, ∫ X : Fin (k + 1) → Fin a → ℂ, F (blockLowerGL (Matrix.of X) *
          blockDiagGL κ₁
            (chartGL w * iotaGL (τ : Langlands.GeneralLinear k ℂ)))
        = ∫ q, f q := (integral_prod f hf).symm
      _ = ∫ q, f (rowsChart a k q) := integral_rowsChart f
      _ = ∫ X' : Fin k → Fin a → ℂ, ∫ v : Fin (a + k) → ℂ, f (rowsChart a k (X', v)) :=
          integral_prod _ (integrable_rowsChart hf)
      _ = _ := by simp_rw [hfr]
  calc ∫ κ₂ : unitaryCompact ℂ (k + 1), (∫ X : Fin (k + 1) → Fin a → ℂ,
        F (blockLowerGL (Matrix.of X) * blockDiagGL κ₁
          (κ₂ : Langlands.GeneralLinear (k + 1) ℂ))) ∂unitaryHaar (k + 1)
      = ∫ κ₂ : unitaryCompact ℂ (k + 1), (∫ X : Fin (k + 1) → Fin a → ℂ,
          sliceT F (slicePoint κ₁ X) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ))
          ∂unitaryHaar (k + 1) :=
        integral_congr_ae (ae_of_all _ h2a)
    _ = ∫ X : Fin (k + 1) → Fin a → ℂ, (∫ κ₂ : unitaryCompact ℂ (k + 1),
          sliceT F (slicePoint κ₁ X) (κ₂ : Langlands.GeneralLinear (k + 1) ℂ)
            ∂unitaryHaar (k + 1)) :=
        integral_integral_swap hjoint2
    _ = ∫ X : Fin (k + 1) → Fin a → ℂ, (chartConstant k : ℂ) * ∫ q, sliceT F (slicePoint κ₁ X)
          (chartGL q.2 * iotaGL (q.1 : Langlands.GeneralLinear k ℂ)) ∂μq :=
        integral_congr_ae (ae_of_all _ h2c)
    _ = (chartConstant k : ℂ) * ∫ q, (∫ X : Fin (k + 1) → Fin a → ℂ, sliceT F (slicePoint κ₁ X)
          (chartGL q.2 * iotaGL (q.1 : Langlands.GeneralLinear k ℂ))) ∂μq := by
        rw [integral_const_mul, integral_integral_swap hjoint3]
    _ = (chartConstant k : ℂ) * ∫ q, (∫ X : Fin (k + 1) → Fin a → ℂ,
          F (blockLowerGL (Matrix.of X) * blockDiagGL κ₁
            (chartGL q.2 * iotaGL (q.1 : Langlands.GeneralLinear k ℂ)))) ∂μq := by
        rw [integral_congr_ae (ae_of_all _ h2f)]
    _ = (chartConstant k : ℂ) * ∫ τ : unitaryCompact ℂ k, (∫ w : Fin k → ℂ,
          ∫ X : Fin (k + 1) → Fin a → ℂ, F (blockLowerGL (Matrix.of X) *
            blockDiagGL κ₁
              (chartGL w * iotaGL (τ : Langlands.GeneralLinear k ℂ)))) ∂unitaryHaar k := by
        rw [integral_prod _ hint3]
    _ = _ := by simp_rw [h2h]

/-- **Step 2.** The right side of the formula for `P_{a,k+1}` is `c_k Z(F)`. -/
theorem step_two (hF : F ∈ principalSeries ℂ (a + (k + 1)) (modulusCharacter (a + (k + 1)))) :
    ∫ κ₁ : unitaryCompact ℂ a, (∫ κ₂ : unitaryCompact ℂ (k + 1),
      (∫ X : Fin (k + 1) → Fin a → ℂ,
        F (blockLowerGL (Matrix.of X) * blockDiagGL (κ₁ : Langlands.GeneralLinear a ℂ)
          (κ₂ : Langlands.GeneralLinear (k + 1) ℂ))) ∂unitaryHaar (k + 1)) ∂unitaryHaar a =
      (chartConstant k : ℂ) * chartIntegral F := by
  rw [chartIntegral, ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun κ₁ => step_two_inner hF κ₁.2)

end StepTwo

/-! ## The induction -/

/-- The induction step: the formula for `P_{a,k}` implies the formula for `P_{a,k+1}`, with
`c_{a,k+1} = c_{a+k} c_{a,k} / c_k`. -/
theorem blockFormula_succ {a k : ℕ} (hIH : BlockFormula a k) : BlockFormula a (k + 1) := by
  obtain ⟨c₀, hc₀, h1⟩ := step_one hIH
  refine ⟨chartConstant (a + k) * c₀ / chartConstant k,
    div_pos (mul_pos (chartConstant_pos _) hc₀) (chartConstant_pos k), fun F hF => ?_⟩
  rw [h1 F hF, step_two hF]
  have hc : (chartConstant k : ℂ) ≠ 0 := by exact_mod_cast (chartConstant_pos k).ne'
  push_cast
  field_simp

theorem blockFormula (a : ℕ) : ∀ k : ℕ, BlockFormula a k
  | 0 => blockFormula_zero a
  | k + 1 => blockFormula_succ (blockFormula a k)

end ComplexBlockParabolicProof

/-- **Statement (the induction step of the integration formula along `P_{a,k}`).** For all
`a, k ∈ ℕ`, if the formula
`∫_{U(a+k)} F = c ∫_{U(a)} ∫_{U(k)} ∫_{M_{k×a}(ℂ)} F(n̄(X) diag(κ₁, κ₂)) dX dκ₂ dκ₁` holds with some
`c > 0` for all `F` in the principal series of the modulus character of `GL_{a+k}(ℂ)`
(`ComplexBlockParabolicProof.BlockFormula a k`), then the corresponding formula holds for `a` and
`k + 1`. -/
def ComplexBlockParabolicStepStatement : Prop :=
  ∀ a k : ℕ, ComplexBlockParabolicProof.BlockFormula a k →
    ComplexBlockParabolicProof.BlockFormula a (k + 1)

theorem complexBlockParabolicStep : ComplexBlockParabolicStepStatement :=
  fun _ _ => ComplexBlockParabolicProof.blockFormula_succ

/-- **Proof of `ComplexBlockParabolicIntegrationStatement`.** -/
theorem complexBlockParabolicIntegration : ComplexBlockParabolicIntegrationStatement := by
  intro a k
  obtain ⟨c, hc, h⟩ := ComplexBlockParabolicProof.blockFormula a k
  exact ⟨c, hc, fun F hF => ⟨ComplexBlockParabolicProof.integrable_clause hF, h F hF⟩⟩

end Langlands.Archimedean
