import Langlands.Analysis.SchwartzAngularAverage
import Langlands.Analysis.SchwartzCoordinateMellinContinuation
import Langlands.Representation.GodementJacquet.ComplexCoordinateFourier

/-! # Diagonal complex zeta integrals and their Mellin continuation -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Analysis
open Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal

variable {ι : Type*} [Fintype ι]

local notation "Z" => ι → ℂ
local notation "R" => ι → ℝ

/-- The single-coordinate complex Mellin weight, with the multiplicative Haar
density incorporated into the weight for the additive measure. -/
def complexMellinWeight (m : ℤ) (u : ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else (z / (‖z‖ : ℂ)) ^ m * (‖z‖ : ℂ) ^ (2 * u - 2)

theorem measurable_complexMellinWeight (m : ℤ) (u : ℂ) :
    Measurable (complexMellinWeight m u) := by
  unfold complexMellinWeight
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  fun_prop

/-- The complex diagonal zeta kernel in additive coordinates. -/
def complexDiagonalZetaKernel (Φ : Z → ℂ) (m : ι → ℤ) (u : Z) (z : Z) : ℂ :=
  Φ z * ∏ i, complexMellinWeight (m i) (u i) (z i)

theorem measurable_complexDiagonalZetaKernel {Φ : Z → ℂ} (hΦ : Measurable Φ)
    (m : ι → ℤ) (u : Z) : Measurable (complexDiagonalZetaKernel Φ m u) :=
  hΦ.mul (Finset.measurable_prod _ fun i _ =>
    (measurable_complexMellinWeight (m i) (u i)).comp (measurable_pi_apply i))

private def polarPoint (p : R × R) : Z :=
  fun i => complexAngularPhase (p.2 i) * (p.1 i : ℂ)

omit [Fintype ι] in
private theorem continuous_polarPoint : Continuous (polarPoint (ι := ι)) := by
  unfold polarPoint complexAngularPhase
  fun_prop

omit [Fintype ι] in
private theorem norm_polarPoint (p : R × R) (i : ι) : ‖polarPoint p i‖ = ‖p.1 i‖ := by
  simp only [polarPoint, norm_mul, norm_complexAngularPhase, one_mul, Complex.norm_real]

omit [Fintype ι] in
private theorem polarPoint_eq (p : R × R) :
    (fun i => Complex.polarCoord.symm (pairPolarCoordinates p i)) = polarPoint p := by
  ext i
  rw [pairPolarCoordinates_apply p.1 p.2, Complex.polarCoord_symm_apply]
  change (p.1 i : ℂ) * (Real.cos (p.2 i) + Real.sin (p.2 i) * Complex.I) = polarPoint p i
  rw [polarPoint, complexAngularPhase, Complex.exp_ofReal_mul_I, mul_comm]

private def polarDiagonalKernel (Φ : Z → ℂ) (m : ι → ℤ) (u : Z) (p : R × R) : ℂ :=
  Φ (polarPoint p) * (∏ i, (p.1 i : ℂ) ^ (2 * u i - 1)) * complexAngularWeight m p.2

private theorem integrable_polarDiagonalKernel (Φ : SchwartzMap Z ℂ) (m : ι → ℤ)
    {u : Z} (hu : ∀ i, 0 < (u i).re) :
    Integrable (polarDiagonalKernel Φ m u)
      ((positiveCoordinateMeasure ι).prod (angularCoordinateMeasure ι)) := by
  let v (i : ι) := 2 * u i
  have hv (i : ι) : 0 < (v i).re := by
    simp only [v, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    positivity [hu i]
  obtain ⟨b, hb⟩ := Finite.exists_le (fun i => (v i).re)
  obtain ⟨q, hq⟩ := exists_nat_gt b
  obtain ⟨C, hC₀, hC⟩ := exists_schwartz_norm_le_coordinate_decay Φ q
  have h := Integrable.fintype_prod (fun i =>
    integrable_positiveLine_damped_cpow (hv i) q ((hb i).trans_lt hq))
  have hI := (h.const_mul C).comp_fst (angularCoordinateMeasure ι)
  have hmeas : Measurable (polarDiagonalKernel Φ m u) :=
    ((Φ.continuous.comp continuous_polarPoint).measurable.mul (Finset.measurable_prod _ fun i _ =>
      (measurable_ofReal_cpow_const (2 * u i - 1)).comp
        ((measurable_pi_apply i).comp measurable_fst))).mul
      ((continuous_complexAngularWeight m).measurable.comp measurable_snd)
  refine hI.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  change ‖polarDiagonalKernel Φ m u p‖ ≤ C *
    ∏ i, ‖(p.1 i : ℂ) ^ (v i - 1)‖ * ((1 + ‖p.1 i‖) ^ q)⁻¹
  simp only [polarDiagonalKernel, norm_mul, norm_complexAngularWeight, mul_one, Complex.norm_prod,
    Finset.prod_mul_distrib, ← mul_assoc]
  rw [mul_right_comm C]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  simpa only [norm_polarPoint] using hC (polarPoint p)

private theorem complexMellinWeight_polar (r θ : ℝ) (hr : 0 < r) (m : ℤ) (u : ℂ) :
    (r : ℂ) * complexMellinWeight m u (complexAngularPhase θ * (r : ℂ)) =
      (r : ℂ) ^ (2 * u - 1) * complexAngularPhase (m * θ) := by
  have hr₀ : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have he : complexAngularPhase θ ≠ 0 := Complex.exp_ne_zero ((θ : ℂ) * Complex.I)
  have hn : ‖complexAngularPhase θ * (r : ℂ)‖ = r := by
    rw [norm_mul, norm_complexAngularPhase, one_mul, Complex.norm_of_nonneg hr.le]
  rw [complexMellinWeight, ite_eq_right (mul_ne_zero he hr₀), hn, mul_div_cancel_right₀ _ hr₀]
  have hp : (r : ℂ) * (r : ℂ) ^ (2 * u - 2) = (r : ℂ) ^ (2 * u - 1) := by
    calc
      _ = (r : ℂ) ^ (1 : ℂ) * (r : ℂ) ^ (2 * u - 2) := by rw [Complex.cpow_one]
      _ = _ := by rw [← Complex.cpow_add _ _ hr₀]; congr 1; ring
  have hm : complexAngularPhase θ ^ m = complexAngularPhase (m * θ) := by
    rw [complexAngularPhase, ← Complex.exp_int_mul]
    unfold complexAngularPhase
    push_cast
    ring_nf
  rw [hm, mul_left_comm, hp, mul_comm]

private theorem polarDiagonalKernel_eq (Φ : Z → ℂ) (m : ι → ℤ) (u : Z)
    (p : R × R) (hp : ∀ i, 0 < p.1 i) :
    (∏ i, p.1 i) • complexDiagonalZetaKernel Φ m u (polarPoint p) =
      polarDiagonalKernel Φ m u p := by
  simp only [Complex.real_smul, Complex.ofReal_prod, complexDiagonalZetaKernel, polarDiagonalKernel,
    complexAngularWeight, polarPoint, mul_left_comm (∏ i, (p.1 i : ℂ)), mul_assoc,
    ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun i _ => complexMellinWeight_polar _ _ (hp i) _ _

private theorem integrable_complexDiagonalZetaKernel_volume (Φ : SchwartzMap Z ℂ)
    (m : ι → ℤ) {u : Z} (hu : ∀ i, 0 < (u i).re) :
    Integrable (complexDiagonalZetaKernel Φ m u) volume := by
  let F := complexDiagonalZetaKernel Φ m u
  have hI := integrable_polarDiagonalKernel Φ m hu
  refine ⟨(measurable_complexDiagonalZetaKernel Φ.continuous.measurable m u).aestronglyMeasurable,
    ?_⟩
  rw [hasFiniteIntegral_iff_norm, ← Complex.lintegral_comp_pi_polarCoord_symm]
  rw [← measurePreserving_pairPolarCoordinates.lintegral_comp_emb
    (pairPolarCoordinates (ι := ι)).measurableEmbedding]
  convert (hasFiniteIntegral_iff_norm _).1 hI.hasFiniteIntegral using 1
  apply lintegral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae ae_positiveCoordinates] with p hp
  change (∏ i, ENNReal.ofReal (p.1 i)) * ENNReal.ofReal ‖F
    (fun i => Complex.polarCoord.symm (pairPolarCoordinates p i))‖ =
      ENNReal.ofReal ‖polarDiagonalKernel Φ m u p‖
  have h₀ : 0 ≤ ∏ i, p.1 i := Finset.prod_nonneg fun i _ => (hp i).le
  rw [polarPoint_eq, ← polarDiagonalKernel_eq Φ m u p hp, norm_smul, Real.norm_of_nonneg h₀,
    ENNReal.ofReal_mul h₀, ENNReal.ofReal_prod_of_nonneg (fun i _ => (hp i).le)]

private theorem integral_complexDiagonalZetaKernel_volume (Φ : SchwartzMap Z ℂ)
    (m : ι → ℤ) {u : Z} (hu : ∀ i, 0 < (u i).re) :
    (∫ z, complexDiagonalZetaKernel Φ m u z) =
      coordinateMellin (schwartzAngularAverage m Φ) (fun i => 2 * u i) := by
  have hI := integrable_polarDiagonalKernel Φ m hu
  rw [← Complex.integral_comp_pi_polarCoord_symm, ← measurePreserving_pairPolarCoordinates.integral_comp']
  calc
    _ = ∫ p : R × R, polarDiagonalKernel Φ m u p
        ∂(positiveCoordinateMeasure ι).prod (angularCoordinateMeasure ι) := by
      apply integral_congr_ae
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae ae_positiveCoordinates] with p hp
      change (∏ i, p.1 i) • complexDiagonalZetaKernel Φ m u
        (fun i => Complex.polarCoord.symm (pairPolarCoordinates p i)) = _
      rw [polarPoint_eq, polarDiagonalKernel_eq Φ m u p hp]
    _ = _ := by
      rw [integral_prod _ hI, coordinateMellin]
      apply integral_congr_ae
      exact Eventually.of_forall fun r => by
        change (∫ θ, polarDiagonalKernel Φ m u (r, θ) ∂angularCoordinateMeasure ι) =
          coordinateMellinIntegrand (schwartzAngularAverage m Φ) (fun i => 2 * u i) r
        rw [coordinateMellinIntegrand, schwartzAngularAverage_apply, ← integral_mul_const]
        apply integral_congr_ae
        exact Eventually.of_forall fun θ => by
          change polarDiagonalKernel Φ m u (r, θ) =
            (complexAngularWeight m θ * Φ (polarPoint (r, θ))) *
              ∏ i, (r i : ℂ) ^ (2 * u i - 1)
          rw [polarDiagonalKernel]
          ring

/-- The scalar by which the self-dual product measure scales ordinary volume. -/
def complexCoordinateMeasureScale (ι : Type*) [Fintype ι] (a : ℂˣ) : NNReal :=
  (‖(a : ℂ)‖₊ * 2) ^ Fintype.card ι

theorem complexCoordinateMeasure_eq_smul_volume (a : ℂˣ) :
    complexCoordinateMeasure ι a =
      complexCoordinateMeasureScale ι a • (volume : Measure Z) := by
  let : (complexSelfDualMeasure a).measure.IsAddHaarMeasure := (complexSelfDualMeasure a).isAddHaar
  unfold complexCoordinateMeasure
  apply Measure.pi_eq
  intro s _
  simp only [complexSelfDualMeasure, complexScaledMeasure_measure, Measure.smul_apply, volume_pi,
    Measure.pi_pi, complexCoordinateMeasureScale]
  change (↑((‖(a : ℂ)‖₊ * 2) ^ Fintype.card ι) : ENNReal) * (∏ i, volume (s i)) =
    ∏ i, (↑(‖(a : ℂ)‖₊ * 2) : ENNReal) * volume (s i)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

/-- Initial absolute convergence of the complex product zeta integral. -/
theorem integrable_complexDiagonalZetaKernel (a : ℂˣ) (Φ : SchwartzMap Z ℂ) (m : ι → ℤ)
    {u : Z} (hu : ∀ i, 0 < (u i).re) :
    Integrable (complexDiagonalZetaKernel Φ m u) (complexCoordinateMeasure ι a) := by
  rw [complexCoordinateMeasure_eq_smul_volume]
  exact (integrable_complexDiagonalZetaKernel_volume Φ m hu).smul_measure ENNReal.coe_ne_top

/-- The continued complex diagonal zeta integral. -/
def complexDiagonalZeta (a : ℂˣ) (Φ : SchwartzMap Z ℂ) (m : ι → ℤ) (u : Z) : ℂ :=
  (complexCoordinateMeasureScale ι a : ℂ) *
    coordinateMellinContinuation (schwartzAngularAverage m Φ) (fun i => 2 * u i)

/-- The meromorphic diagonal integral agrees with the original integral on its
domain of absolute convergence. -/
theorem complexDiagonalZeta_eq_integral (a : ℂˣ) (Φ : SchwartzMap Z ℂ) (m : ι → ℤ)
    {u : Z} (hu : ∀ i, 0 < (u i).re) :
    complexDiagonalZeta a Φ m u =
      ∫ z, complexDiagonalZetaKernel Φ m u z ∂complexCoordinateMeasure ι a := by
  have h (i : ι) : 0 < (2 * u i).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    positivity [hu i]
  rw [complexDiagonalZeta, coordinateMellinContinuation_eq _ h,
    complexCoordinateMeasure_eq_smul_volume, integral_smul_nnreal_measure,
    integral_complexDiagonalZetaKernel_volume Φ m hu]
  rfl

/-- Meromorphic continuation on affine lines of independent complex exponents. -/
theorem meromorphic_complexDiagonalZeta_affine (a : ℂˣ) (Φ : SchwartzMap Z ℂ) (m : ι → ℤ)
    (c : R) (b : Z) :
    Meromorphic (fun z : ℂ => complexDiagonalZeta a Φ m (fun i => (c i : ℂ) * z + b i)) := by
  have h := meromorphic_coordinateMellinContinuation_affine (schwartzAngularAverage m Φ)
    (fun i => 2 * c i) (fun i => 2 * b i)
  intro z
  convert (MeromorphicAt.const (complexCoordinateMeasureScale ι a : ℂ) z).mul (h z) using 1
  ext1 w
  simp only [complexDiagonalZeta, Pi.mul_apply, Complex.ofReal_mul, Complex.ofReal_ofNat,
    mul_add, mul_assoc]

/-- The continued complex diagonal zeta integral is analytic off the
possible radial Mellin poles. -/
theorem analyticAt_complexDiagonalZeta_affine (a : ℂˣ) (Φ : SchwartzMap Z ℂ) (m : ι → ℤ)
    (c : R) (b : Z) {z : ℂ}
    (hz : ∀ (i : ι) (j : ℕ), 2 * ((c i : ℂ) * z + b i) + (j : ℂ) ≠ 0) :
    AnalyticAt ℂ (fun w : ℂ => complexDiagonalZeta a Φ m (fun i => (c i : ℂ) * w + b i)) z := by
  have hf (w : ℂ) (i : ι) :
      (((2 * c i : ℝ) : ℂ) * w + 2 * b i) = 2 * ((c i : ℂ) * w + b i) := by
    push_cast
    ring
  have h := analyticAt_coordinateMellinContinuation_affine (schwartzAngularAverage m Φ)
    (fun i => 2 * c i) (fun i => 2 * b i)
    (fun i j => by rw [hf]; exact hz i j)
  unfold complexDiagonalZeta
  simp only [← hf]
  exact analyticAt_const.mul h

end Langlands.GodementJacquet
