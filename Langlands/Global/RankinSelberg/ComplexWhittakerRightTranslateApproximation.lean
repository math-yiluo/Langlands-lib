import Langlands.Global.RankinSelberg.ComplexWhittakerTranslateExtension

/-! # Positive compact approximation of complex Whittaker right translates -/

noncomputable section

open MeasureTheory Filter
open scoped Topology Matrix.Norms.Operator Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexWhittakerRightTranslateApproximation

open Langlands.Archimedean (matrixModel continuous_unitary_toUnits)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexGodement (compactMatrixHaar)
open ComplexCentralPolynomialWeight (complexCentralPolynomialWeight)
open ComplexCompactDifferenceDensity (convolution_error)
open ComplexWhittakerSmoothExtension (exists_smooth_compact_difference_bound)
open ComplexWhittakerTranslateExtension (exists_polynomial_projection)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℂ
local notation "Std" => Automorphic.complexStandardKFinite

local instance rightTranslateApproximationMeasurable (n : ℕ) : MeasurableSpace (K n) := borel _
local instance rightTranslateApproximationBorel (n : ℕ) : BorelSpace (K n) := ⟨rfl⟩

/-- A right translate of an exact Whittaker vector is the pointwise limit of finite model
vectors obtained by positive compact averages of that translate. -/
def ComplexWhittakerRightTranslateApproximationStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ)
    (B : Std (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)), IsComplexWhittakerIntertwiner r ds a B →
  ∀ (f : Std (r + 1) ds) (g : G (r + 1)),
    ∃ (U : ℕ → complexWhittakerModel r ds a) (w : ℕ → K (r + 1) → ℝ),
      (∀ j, Continuous (w j)) ∧ (∀ j k, 0 ≤ w j k) ∧
      (∀ j, (∫ k, w j k ∂compactMatrixHaar (r + 1)) = 1) ∧
      (∀ j x, (U j).val x = ∫ k, (w j k : ℂ) * B f (x * Unitary.toUnits k * g)
        ∂compactMatrixHaar (r + 1)) ∧
      ∀ x, Tendsto (fun j => (U j).val x) atTop (𝓝 (B f (x * g)))

set_option maxHeartbeats 900000 in
theorem complexWhittakerRightTranslateApproximation : ComplexWhittakerRightTranslateApproximationStatement := by
  intro r ds a B hB f g
  let n := r + 1
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  choose w wR hw hc hPos hwR hCentral hMass hMoment using fun j : ℕ =>
    complexCentralPolynomialWeight n (ε j) (hε j)
  choose p _ hp using fun j : ℕ => exists_polynomial_projection r ds a B hB (w j) (hw j) f g
  let U (j : ℕ) : complexWhittakerModel r ds a :=
    ⟨B (p j), Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨p j, rfl⟩)⟩
  refine ⟨U, wR, hc, hPos, hMass, ?_, ?_⟩
  · intro j x
    change B (p j) x = _
    rw [hp j x]
    apply integral_congr_ae
    exact ae_of_all _ fun k => by
      change w j k * _ = (wR j k : ℂ) * _
      rw [hwR j k]
  · intro x
    let F : G n → ℂ := fun z => B f (x * z * g)
    let φ : K n → ℂ := fun k => F (Unitary.toUnits k)
    have hF : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ F :=
      ((hB.2.1 f).comp contMDiff_mul_right).comp contMDiff_mul_left
    have hφ : Continuous φ := hF.continuous.comp continuous_unitary_toUnits
    obtain ⟨C, hC, hφC⟩ := exists_smooth_compact_difference_bound hF 1
    have hBd (j : ℕ) : dist ((U j).val x) (B f (x * g)) ≤ C * ε j := by
      have hCj := convolution_error (w j) (wR j) (hc j) (hPos j) (hwR j)
        (hCentral j) (hMass j) hφ hC hφC (hMoment j).le [] le_rfl 1
      change ‖ComplexCompactDifferenceDensity.convolution (w j) φ 1 - φ 1‖ ≤ C * ε j * 1 at hCj
      have hφ₁ : φ 1 = B f (x * g) := by simp [φ, F]
      have hConv : ComplexCompactDifferenceDensity.convolution (w j) φ 1 = B (p j) x := by
        rw [hp j x]
        unfold ComplexCompactDifferenceDensity.convolution
        simp only [one_mul]
        rfl
      rw [dist_eq_norm]
      simpa only [U, hConv, hφ₁, mul_one] using hCj
    apply tendsto_iff_dist_tendsto_zero.mpr
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ => dist_nonneg) hBd
    have hLim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hConst : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
    simpa only [mul_zero] using hConst.mul hLim

end Langlands.Global.RankinSelbergGlobal.ComplexWhittakerRightTranslateApproximation
