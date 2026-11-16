import Langlands.Representation.Archimedean.ComplexBlockModulusBound
import Langlands.Representation.Archimedean.ComplexBlockDual

/-!
# Slices and norm integrals for the block integration formula

Tools for the proof of `ComplexBlockParabolicIntegrationStatement`, for a function `F` of the
principal series of the modulus character of `GL_{m+1}(ℂ)` or of `GL_{a+k+1}(ℂ)`:

* `chartNorm F g = ∫_{ℂ^m} ‖F(J(v,1) ι(g))‖ dv` is norm-covariant on `GL_m(ℂ)` and bounded on
  `U(m)`; `v ↦ F(J(v,1) ι(g))` is integrable for every `g`;
* `blockNorm F κ₁ h = ∫_{M_{(k+1)×a}} ‖F(n̄(X) diag(κ₁, h))‖ dX` is norm-covariant on
  `GL_{k+1}(ℂ)` and bounded on `U(k+1)`; `X ↦ F(n̄(X) diag(κ₁, h))` is integrable for every `h`;
* the slice `sliceT F y h = F(diag(1, h) y) |det h|^{2a}` lies in the principal series of the
  modulus character of `GL_{k+1}(ℂ)`.
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

/-! ## Exponent arithmetic -/

section Exponents

theorem rpow_modExp_succ {m : ℕ} {x : ℝ} (hx : 0 < x) (l : ℕ) :
    x ^ modExp (m + 1) l * (x ^ 2)⁻¹ = x ^ modExp m l := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_neg hx.le, ← Real.rpow_add hx]
  congr 1
  unfold modExp
  push_cast
  ring

theorem rpow_modExp_block {a k : ℕ} {x : ℝ} (hx : 0 < x) (j : ℕ) :
    x ^ modExp (a + (k + 1)) (a + j) * (x ^ 2) ^ a = x ^ modExp (k + 1) j := by
  rw [← pow_mul, ← Real.rpow_natCast x (2 * a), ← Real.rpow_add hx]
  congr 1
  unfold modExp
  push_cast
  ring

end Exponents

/-! ## The chart norm -/

section ChartNorm

variable {m : ℕ} {F : Langlands.GeneralLinear (m + 1) ℂ → ℂ}

theorem iotaGL_borel (z : Fin m → ℂˣ) (u : upperUnipotent m ℂ) :
    iotaGL ((Iwasawa.diagonalUnits z : Langlands.GeneralLinear m ℂ) *
      (u : Langlands.GeneralLinear m ℂ)) =
      (Iwasawa.diagonalUnits (fun i => Fin.lastCases 1 z i) : Langlands.GeneralLinear (m + 1) ℂ) *
        ((⟨iotaGL (u : Langlands.GeneralLinear m ℂ), iotaGL_mem_upperUnipotent u⟩ :
          upperUnipotent (m + 1) ℂ) : Langlands.GeneralLinear (m + 1) ℂ) := by
  rw [map_mul, iotaGL_diagonalUnits]

theorem det_borel {N : ℕ} (z : Fin N → ℂˣ) (u : upperUnipotent N ℂ) :
    (((Iwasawa.diagonalUnits z : Langlands.GeneralLinear N ℂ) *
      (u : Langlands.GeneralLinear N ℂ) : Langlands.GeneralLinear N ℂ) :
        Matrix (Fin N) (Fin N) ℂ).det = ∏ i, (z i : ℂ) := by
  rw [Units.val_mul, Matrix.det_mul, det_upperUnipotent, Iwasawa.diagonalUnits_val,
    Matrix.det_diagonal, mul_one]

theorem det_borel_ne_zero {N : ℕ} (z : Fin N → ℂˣ) (u : upperUnipotent N ℂ) :
    (((Iwasawa.diagonalUnits z : Langlands.GeneralLinear N ℂ) *
      (u : Langlands.GeneralLinear N ℂ) : Langlands.GeneralLinear N ℂ) :
        Matrix (Fin N) (Fin N) ℂ).det ≠ 0 := by
  rw [det_borel]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => (z i).ne_zero

theorem norm_chart_iota_borel (hF : NormCov (m + 1) F) (z : Fin m → ℂˣ) (u : upperUnipotent m ℂ)
    (g : Langlands.GeneralLinear m ℂ) (v : Fin m → ℂ) :
    ‖F (chartGL v * iotaGL ((Iwasawa.diagonalUnits z : Langlands.GeneralLinear m ℂ) *
      (u : Langlands.GeneralLinear m ℂ) * g))‖ =
      (∏ l : Fin m, ‖(z l : ℂ)‖ ^ modExp (m + 1) l) *
        ‖F (chartGL (v ᵥ* (((Iwasawa.diagonalUnits z : Langlands.GeneralLinear m ℂ) *
          (u : Langlands.GeneralLinear m ℂ) : Langlands.GeneralLinear m ℂ) :
            Matrix (Fin m) (Fin m) ℂ)) * iotaGL g)‖ := by
  rw [map_mul iotaGL _ g, ← mul_assoc, chartGL_mul_iotaGL, mul_assoc, iotaGL_borel, hF]
  congr 1
  rw [Fin.prod_univ_castSucc]
  simp

/-- `N(g) = ∫_{ℂ^m} ‖F(J(v,1) ι(g))‖ dv`. -/
def chartNorm (F : Langlands.GeneralLinear (m + 1) ℂ → ℂ) (g : Langlands.GeneralLinear m ℂ) : ℝ :=
  ∫ v : Fin m → ℂ, ‖F (chartGL v * iotaGL g)‖

theorem chartNorm_nonneg (F : Langlands.GeneralLinear (m + 1) ℂ → ℂ)
    (g : Langlands.GeneralLinear m ℂ) : 0 ≤ chartNorm F g :=
  integral_nonneg fun _ => norm_nonneg _

theorem norm_chartNorm (F : Langlands.GeneralLinear (m + 1) ℂ → ℂ)
    (g : Langlands.GeneralLinear m ℂ) : ‖((chartNorm F g : ℝ) : ℂ)‖ = chartNorm F g := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (chartNorm_nonneg F g)]

theorem prod_norm_inv_sq (z : Fin m → ℂˣ) :
    (∏ l : Fin m, ‖(z l : ℂ)‖ ^ modExp (m + 1) l) * (‖∏ i, (z i : ℂ)‖ ^ 2)⁻¹ =
      ∏ l : Fin m, ‖(z l : ℂ)‖ ^ modExp m l := by
  rw [norm_prod, ← Finset.prod_pow, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun l _ => rpow_modExp_succ (norm_pos_iff.mpr (z l).ne_zero) l

/-- The chart norm is norm-covariant on `GL_m(ℂ)`. -/
theorem normCov_chartNorm (hF : NormCov (m + 1) F) :
    NormCov m fun g => ((chartNorm F g : ℝ) : ℂ) := by
  intro z u g
  rw [norm_chartNorm, norm_chartNorm]
  unfold chartNorm
  simp_rw [norm_chart_iota_borel hF]
  rw [integral_const_mul, integral_vecMul_smul (det_borel_ne_zero z u)
    (fun v => ‖F (chartGL v * iotaGL g)‖), smul_eq_mul, ← mul_assoc, det_borel,
    prod_norm_inv_sq]

theorem chartNorm_le (hF : NormCov (m + 1) F) {C : ℝ}
    (hC : ∀ κ ∈ unitaryCompact ℂ (m + 1), ‖F κ‖ ≤ C) {κ : Langlands.GeneralLinear m ℂ}
    (hκ : κ ∈ unitaryCompact ℂ m) :
    chartNorm F κ ≤ C * ∫ x : Fin m → ℂ, ∏ l : Fin m, (1 + ‖x l‖ ^ 2) ^ (-2 : ℝ) := by
  rw [chartNorm, ← integral_const_mul]
  exact integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
    (integrable_chartBound.const_mul C)
    (ae_of_all _ fun v => norm_le_chartBound hF hC v (iotaGL_mem_unitaryCompact hκ))

/-- `v ↦ F(J(v,1) ι(g))` is integrable for every `g ∈ GL_m(ℂ)`. -/
theorem integrable_chart_iota (hF : NormCov (m + 1) F) (hc : Continuous F) {C : ℝ}
    (hC : ∀ κ ∈ unitaryCompact ℂ (m + 1), ‖F κ‖ ≤ C) (g : Langlands.GeneralLinear m ℂ) :
    Integrable fun v : Fin m → ℂ => F (chartGL v * iotaGL g) := by
  obtain ⟨z, u, κ, hκ, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
  set P := ∏ l : Fin m, ‖(z l : ℂ)‖ ^ modExp (m + 1) l with hP
  refine Integrable.mono' ((integrable_comp_vecMul (det_borel_ne_zero z u)
    integrable_chartBound).const_mul (P * C))
    ((hc.comp (continuous_chartGL.mul continuous_const)).aestronglyMeasurable)
    (ae_of_all _ fun v => ?_)
  rw [norm_chart_iota_borel hF, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_le_chartBound hF hC _ (iotaGL_mem_unitaryCompact hκ))
    (Finset.prod_nonneg fun l _ => Real.rpow_nonneg (norm_nonneg _) _)

end ChartNorm

/-! ## The block norm -/

section BlockNorm

variable {a k : ℕ} {F : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}

theorem blockDiagGL_borel (z : Fin (k + 1) → ℂˣ) (u : upperUnipotent (k + 1) ℂ) :
    blockDiagGL (1 : Langlands.GeneralLinear a ℂ)
      ((Iwasawa.diagonalUnits z : Langlands.GeneralLinear (k + 1) ℂ) *
        (u : Langlands.GeneralLinear (k + 1) ℂ)) =
      (Iwasawa.diagonalUnits (Fin.addCases (fun _ => 1) z) :
        Langlands.GeneralLinear (a + (k + 1)) ℂ) *
        ((⟨blockDiagGL (1 : Langlands.GeneralLinear a ℂ) (u : Langlands.GeneralLinear (k + 1) ℂ),
          ComplexBlockDual.blockDiagGL_mem_upperUnipotent_right u⟩ :
            upperUnipotent (a + (k + 1)) ℂ) : Langlands.GeneralLinear (a + (k + 1)) ℂ) := by
  rw [← ComplexBlockDual.blockDiagGL_diagonalUnits_right, ← ComplexBlockJacquet.blockDiagGL_mul,
    one_mul]

/-- `n̄(X) diag(κ₁, b h) = diag(1, b) n̄(b⁻¹ X) diag(κ₁, h)`. -/
theorem blockLowerGL_mul_blockDiagGL_mul (X : Matrix (Fin (k + 1)) (Fin a) ℂ)
    (κ₁ : Langlands.GeneralLinear a ℂ) (b h : Langlands.GeneralLinear (k + 1) ℂ) :
    blockLowerGL X * blockDiagGL κ₁ (b * h) =
      blockDiagGL 1 b * (blockLowerGL (((b⁻¹ : Langlands.GeneralLinear (k + 1) ℂ) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) * X) * blockDiagGL κ₁ h) := by
  have h1 := blockDiagGL_mul_blockLowerGL b (((b⁻¹ : Langlands.GeneralLinear (k + 1) ℂ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) * X) (1 : Langlands.GeneralLinear a ℂ)
  rw [ComplexBlockDual.blockDiagGL_one_one, mul_one, ← Matrix.mul_assoc, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, Matrix.one_mul] at h1
  rw [show blockDiagGL κ₁ (b * h) = blockDiagGL 1 b * blockDiagGL κ₁ h by
    rw [← ComplexBlockJacquet.blockDiagGL_mul, one_mul], ← mul_assoc, ← h1, mul_assoc]

theorem norm_block_borel (hF : NormCov (a + (k + 1)) F) (κ₁ : Langlands.GeneralLinear a ℂ)
    (z : Fin (k + 1) → ℂˣ) (u : upperUnipotent (k + 1) ℂ) (h : Langlands.GeneralLinear (k + 1) ℂ)
    (X : Matrix (Fin (k + 1)) (Fin a) ℂ) :
    ‖F (blockLowerGL X * blockDiagGL κ₁ ((Iwasawa.diagonalUnits z :
      Langlands.GeneralLinear (k + 1) ℂ) * (u : Langlands.GeneralLinear (k + 1) ℂ) * h))‖ =
      (∏ j : Fin (k + 1), ‖(z j : ℂ)‖ ^ modExp (a + (k + 1)) (a + j)) *
        ‖F (blockLowerGL (((((Iwasawa.diagonalUnits z : Langlands.GeneralLinear (k + 1) ℂ) *
          (u : Langlands.GeneralLinear (k + 1) ℂ))⁻¹ : Langlands.GeneralLinear (k + 1) ℂ) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) * X) * blockDiagGL κ₁ h)‖ := by
  rw [blockLowerGL_mul_blockDiagGL_mul, blockDiagGL_borel, hF]
  congr 1
  rw [Fin.prod_univ_add]
  simp

/-- `N₂(h) = ∫_{M_{(k+1)×a}} ‖F(n̄(X) diag(κ₁, h))‖ dX`. -/
def blockNorm (F : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ) (κ₁ : Langlands.GeneralLinear a ℂ)
    (h : Langlands.GeneralLinear (k + 1) ℂ) : ℝ :=
  ∫ X : Fin (k + 1) → Fin a → ℂ, ‖F (blockLowerGL (Matrix.of X) * blockDiagGL κ₁ h)‖

theorem blockNorm_nonneg (F : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ)
    (κ₁ : Langlands.GeneralLinear a ℂ) (h : Langlands.GeneralLinear (k + 1) ℂ) :
    0 ≤ blockNorm F κ₁ h :=
  integral_nonneg fun _ => norm_nonneg _

theorem norm_blockNorm (F : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ)
    (κ₁ : Langlands.GeneralLinear a ℂ) (h : Langlands.GeneralLinear (k + 1) ℂ) :
    ‖((blockNorm F κ₁ h : ℝ) : ℂ)‖ = blockNorm F κ₁ h := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (blockNorm_nonneg F κ₁ h)]

theorem prod_norm_block (z : Fin (k + 1) → ℂˣ) :
    (∏ j : Fin (k + 1), ‖(z j : ℂ)‖ ^ modExp (a + (k + 1)) (a + j)) *
      ((‖(∏ i, (z i : ℂ))⁻¹‖ ^ 2) ^ a)⁻¹ =
      ∏ j : Fin (k + 1), ‖(z j : ℂ)‖ ^ modExp (k + 1) j := by
  rw [norm_inv, inv_pow, inv_pow, inv_inv, norm_prod, ← Finset.prod_pow, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => rpow_modExp_block (norm_pos_iff.mpr (z j).ne_zero) j

/-- The block norm is norm-covariant on `GL_{k+1}(ℂ)`. -/
theorem normCov_blockNorm (hF : NormCov (a + (k + 1)) F) (κ₁ : Langlands.GeneralLinear a ℂ) :
    NormCov (k + 1) fun h => ((blockNorm F κ₁ h : ℝ) : ℂ) := by
  intro z u h
  rw [norm_blockNorm, norm_blockNorm]
  unfold blockNorm
  simp_rw [norm_block_borel hF κ₁ z u h]
  set b : Langlands.GeneralLinear (k + 1) ℂ :=
    (Iwasawa.diagonalUnits z : Langlands.GeneralLinear (k + 1) ℂ) *
      (u : Langlands.GeneralLinear (k + 1) ℂ) with hb
  set B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
    ((b⁻¹ : Langlands.GeneralLinear (k + 1) ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) with hB
  have hdet : B.det = (∏ i, (z i : ℂ))⁻¹ := by
    rw [hB, Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hb, det_borel]
  have hne : B.det ≠ 0 := by
    rw [hdet]
    exact inv_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => (z i).ne_zero)
  have h2 : ∫ X : Fin (k + 1) → Fin a → ℂ,
      ‖F (blockLowerGL (B * Matrix.of X) * blockDiagGL κ₁ h)‖ =
      ((‖B.det‖ ^ 2) ^ a)⁻¹ *
        ∫ X : Fin (k + 1) → Fin a → ℂ, ‖F (blockLowerGL (Matrix.of X) * blockDiagGL κ₁ h)‖ :=
    integral_leftMul_eq_real hne (fun X => ‖F (blockLowerGL (Matrix.of X) * blockDiagGL κ₁ h)‖)
  rw [integral_const_mul, h2, ← mul_assoc, hdet, prod_norm_block]

theorem blockNorm_le (hF : NormCov (a + (k + 1)) F) {C : ℝ}
    (hC : ∀ κ ∈ unitaryCompact ℂ (a + (k + 1)), ‖F κ‖ ≤ C) {κ₁ : Langlands.GeneralLinear a ℂ}
    (hκ₁ : κ₁ ∈ unitaryCompact ℂ a) {κ : Langlands.GeneralLinear (k + 1) ℂ}
    (hκ : κ ∈ unitaryCompact ℂ (k + 1)) :
    blockNorm F κ₁ κ ≤ C * ∫ X, blockBound a (k + 1) X := by
  rw [blockNorm, ← integral_const_mul]
  exact integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
    ((integrable_blockBound a (k + 1)).const_mul C)
    (ae_of_all _ fun X => norm_le_blockBound hF hC X (blockDiagGL_mem_unitaryCompact' hκ₁ hκ))

theorem continuous_blockLowerGL_of :
    Continuous fun X : Fin (k + 1) → Fin a → ℂ => blockLowerGL (a := a) (Matrix.of X) :=
  ComplexBlockLimit.continuous_blockLowerGL

/-- `X ↦ F(n̄(X) diag(κ₁, h))` is integrable for every `h ∈ GL_{k+1}(ℂ)`. -/
theorem integrable_block_diag (hF : NormCov (a + (k + 1)) F) (hc : Continuous F) {C : ℝ}
    (hC : ∀ κ ∈ unitaryCompact ℂ (a + (k + 1)), ‖F κ‖ ≤ C) {κ₁ : Langlands.GeneralLinear a ℂ}
    (hκ₁ : κ₁ ∈ unitaryCompact ℂ a) (h : Langlands.GeneralLinear (k + 1) ℂ) :
    Integrable fun X : Fin (k + 1) → Fin a → ℂ =>
      F (blockLowerGL (Matrix.of X) * blockDiagGL κ₁ h) := by
  obtain ⟨z, u, κ, hκ, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitary h
  set b : Langlands.GeneralLinear (k + 1) ℂ :=
    (Iwasawa.diagonalUnits z : Langlands.GeneralLinear (k + 1) ℂ) *
      (u : Langlands.GeneralLinear (k + 1) ℂ) with hb
  have hne : ((b⁻¹ : Langlands.GeneralLinear (k + 1) ℂ) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)).ne_zero
  set P := ∏ j : Fin (k + 1), ‖(z j : ℂ)‖ ^ modExp (a + (k + 1)) (a + j) with hP
  refine Integrable.mono' ((integrable_comp_leftMul hne (integrable_blockBound a (k + 1))).const_mul
    (P * C))
    ((hc.comp (continuous_blockLowerGL_of.mul continuous_const)).aestronglyMeasurable)
    (ae_of_all _ fun X => ?_)
  rw [norm_block_borel hF κ₁ z u κ, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_
    (Finset.prod_nonneg fun l _ => Real.rpow_nonneg (norm_nonneg _) _)
  exact norm_le_blockBound hF hC (((b⁻¹ : Langlands.GeneralLinear (k + 1) ℂ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) * Matrix.of X) (blockDiagGL_mem_unitaryCompact' hκ₁ hκ)

end BlockNorm

/-! ## The slices along `GL_{k+1}(ℂ)` -/

section Slice

variable {a k : ℕ} {F : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ}

/-- `T(h) = F(diag(1, h) y) |det h|^{2a}`. -/
def sliceT (F : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ)
    (y : Langlands.GeneralLinear (a + (k + 1)) ℂ) (h : Langlands.GeneralLinear (k + 1) ℂ) : ℂ :=
  F (blockDiagGL (1 : Langlands.GeneralLinear a ℂ) h * y) *
    normSqC (h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ).det ^ a

theorem contMDiff_normSqC_det_pow {N : ℕ} (p : ℕ) :
    ContMDiff (matrixModel ℂ N) 𝓘(ℝ, ℂ) ∞ fun h : Langlands.GeneralLinear N ℂ =>
      normSqC (h : Matrix (Fin N) (Fin N) ℂ).det ^ p := by
  refine contMDiff_of_contDiffOn (ψ := fun Y : Matrix (Fin N) (Fin N) ℂ => normSqC Y.det ^ p)
    ?_ fun g => rfl
  have hn : ContDiff ℝ ∞ fun Y : Matrix (Fin N) (Fin N) ℂ => ‖Y.det‖ ^ 2 :=
    (contDiff_norm_sq ℝ).comp contDiff_det
  exact ((Complex.ofRealCLM.contDiff.comp hn).pow p).contDiffOn

theorem modulusValue_addCases (z : Fin (k + 1) → ℂˣ) :
    modulusValue (a + (k + 1)) (Fin.addCases (fun _ => 1) z) *
      normSqC (∏ i, (z i : ℂ)) ^ a = modulusValue (k + 1) z := by
  rw [modulusValue, modulusValue, Fin.prod_univ_add, normSqC_prod, ← Finset.prod_pow]
  simp only [Fin.addCases_left, Fin.addCases_right, Units.val_one, normSqC_one, Complex.one_cpow,
    Finset.prod_const_one, one_mul, ← Finset.prod_mul_distrib, Fin.val_natAdd]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hz : normSqC (z j : ℂ) ≠ 0 := normSqC_ne_zero (z j).ne_zero
  rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hz]
  congr 1
  push_cast
  ring

/-- The slice `T` lies in the principal series of the modulus character of `GL_{k+1}(ℂ)`. -/
theorem sliceT_mem (hF : F ∈ principalSeries ℂ (a + (k + 1)) (modulusCharacter (a + (k + 1))))
    (y : Langlands.GeneralLinear (a + (k + 1)) ℂ) :
    sliceT F y ∈ principalSeries ℂ (k + 1) (modulusCharacter (k + 1)) := by
  have hFy := rightTranslation_mem_principalSeries (χ := modulusCharacter (a + (k + 1))) hF y
  refine ⟨contMDiff_mul_fun ?_ (contMDiff_normSqC_det_pow a), fun z u h => ?_⟩
  · have h1 := ComplexBlockDual.contMDiff_comp_affine hFy.1
      (fun g => blockDiagGL (1 : Langlands.GeneralLinear a ℂ) g) ComplexBlockDual.rightLin
      (ComplexBlockParabolic.blockDiag 1 0) ComplexBlockDual.blockDiagGL_right_val 1
    refine h1.congr fun x => ?_
    rw [one_mul]
    rfl
  · rw [principalSeriesCharacter_modulus]
    unfold sliceT
    have hsplit : blockDiagGL (1 : Langlands.GeneralLinear a ℂ)
        ((Iwasawa.diagonalUnits z : Langlands.GeneralLinear (k + 1) ℂ) *
          (u : Langlands.GeneralLinear (k + 1) ℂ) * h) * y =
        (Iwasawa.diagonalUnits (Fin.addCases (fun _ => 1) z) :
          Langlands.GeneralLinear (a + (k + 1)) ℂ) *
        ((⟨blockDiagGL (1 : Langlands.GeneralLinear a ℂ) (u : Langlands.GeneralLinear (k + 1) ℂ),
          ComplexBlockDual.blockDiagGL_mem_upperUnipotent_right u⟩ :
            upperUnipotent (a + (k + 1)) ℂ) : Langlands.GeneralLinear (a + (k + 1)) ℂ) *
          (blockDiagGL 1 h * y) := by
      rw [show blockDiagGL (1 : Langlands.GeneralLinear a ℂ)
          ((Iwasawa.diagonalUnits z : Langlands.GeneralLinear (k + 1) ℂ) *
            (u : Langlands.GeneralLinear (k + 1) ℂ) * h) =
          blockDiagGL (1 : Langlands.GeneralLinear a ℂ)
            ((Iwasawa.diagonalUnits z : Langlands.GeneralLinear (k + 1) ℂ) *
              (u : Langlands.GeneralLinear (k + 1) ℂ)) * blockDiagGL 1 h by
        rw [← ComplexBlockJacquet.blockDiagGL_mul, one_mul], blockDiagGL_borel]
      simp only [mul_assoc]
    rw [hsplit, covariant hF, Units.val_mul, Matrix.det_mul, det_borel, normSqC_mul, mul_pow,
      ← modulusValue_addCases z]
    ring

theorem sliceT_apply_unitary {y : Langlands.GeneralLinear (a + (k + 1)) ℂ}
    {h : Langlands.GeneralLinear (k + 1) ℂ}
    (hh : ‖(h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ).det‖ = 1) :
    sliceT F y h = F (blockDiagGL (1 : Langlands.GeneralLinear a ℂ) h * y) := by
  rw [sliceT, normSqC, hh]
  simp

end Slice

end ComplexBlockParabolicProof

open ComplexMaximalParabolicIntegration ComplexBlockParabolic in
/-- **Statement (slices along the Levi factor `GL_{k+1}(ℂ)` of `P_{a,k+1}`).** Let `F` lie in the
principal series of the modulus character of `GL_{a+k+1}(ℂ)` and let `y ∈ GL_{a+k+1}(ℂ)`. Then
`h ↦ F(diag(1, h) y) |det h|^{2a}` lies in the principal series of the modulus character of
`GL_{k+1}(ℂ)`. -/
def ComplexBlockSliceStatement : Prop :=
  ∀ (a k : ℕ) (F : Langlands.GeneralLinear (a + (k + 1)) ℂ → ℂ),
    F ∈ principalSeries ℂ (a + (k + 1))
      (ComplexKIntegralInvariance.modulusCharacter (a + (k + 1))) →
    ∀ y : Langlands.GeneralLinear (a + (k + 1)) ℂ,
      (fun h : Langlands.GeneralLinear (k + 1) ℂ =>
        F (blockDiagGL (1 : Langlands.GeneralLinear a ℂ) h * y) *
          (((‖(h : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ).det‖ ^ 2 : ℝ) : ℂ)) ^ a) ∈
        principalSeries ℂ (k + 1) (ComplexKIntegralInvariance.modulusCharacter (k + 1))

theorem complexBlockSlice : ComplexBlockSliceStatement :=
  fun _ _ _ hF y => ComplexBlockParabolicProof.sliceT_mem hF y

end Langlands.Archimedean
