import Langlands.Global.RankinSelberg.ComplexSquareZetaCoefficientAverage
import Langlands.Global.RankinSelberg.ComplexSquareZetaReflection

/-! # Functional equation for square zeta integrals of complex matrix coefficients -/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.Operator NNReal SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta

open Langlands.Archimedean Langlands.Archimedean.ComplexReverseTwist
open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open ComplexGodement (exists_height_bound_standard)
open ComplexSquareFourier (matrixTransform complexSquareFourierUnitaryAverage)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance squareCoefficientReflectionGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance squareCoefficientReflectionGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩

variable {r : ℕ}
local notation "Rank" => r.succ
local notation "G" => Langlands.GeneralLinear r.succ ℂ
local notation "K" => unitaryCompact ℂ r.succ
local notation "Mat" => Matrix (Fin r.succ) (Fin r.succ) ℂ

private theorem inverseTranspose_eq_conjAut (g : G) : inverseTranspose Rank ℂ g = conjAut g :=
  Units.ext rfl

private theorem height_inverseTranspose (g : G) :
    complexMatrixHeight (inverseTranspose Rank ℂ g) = complexMatrixHeight g := by
  have hi (i j : Fin Rank) : ((inverseTranspose Rank ℂ g)⁻¹ : G) i j = g j i := by
    rw [← map_inv, inverseTranspose_entry, inv_inv]
  simp only [complexMatrixHeight, inverseTranspose_entry, hi]
  rw [Finset.sum_comm]
  simp only [add_comm]

private theorem dual_compactCoefficient (κ : Measure K) (w : K → ℂ) (f : G → ℂ) :
    (fun g => compactCoefficient κ id w f (inverseTranspose Rank ℂ g)) =
      compactCoefficient κ (conjK Rank) w (fun g => f (inverseTranspose Rank ℂ g)) := by
  funext g
  unfold compactCoefficient
  apply integral_congr_ae
  filter_upwards with k
  simp only [inverseTranspose_eq_conjAut, id_eq, map_mul, conjK_val, conjAut_conjAut]

private theorem matrixTransform_leftAverageInv (κ : Measure K) [IsFiniteMeasure κ]
    (a : ℂˣ) (w : K → ℂ) (hw : Continuous w) (Φ : 𝓢(Mat, ℂ)) :
    matrixTransform a (leftAverageInv κ id continuous_id w hw Φ) =
      leftAverageInv κ (conjK Rank) continuous_conjK w hw (matrixTransform a Φ) := by
  let Ψ := leftAverageInv κ id continuous_id w hw Φ
  have hΨ (X : Mat) : Ψ X = ∫ k : K, w k * Φ ((k⁻¹ : K).val.val * X * (1 : K).val.val) ∂κ := by
    change leftAverageInv κ id continuous_id w hw Φ X = _
    rw [leftAverageInv_apply]
    simp only [id_eq, Subgroup.coe_inv, Subgroup.coe_one, Units.val_one, Matrix.mul_one]
  ext X
  have h := complexSquareFourierUnitaryAverage κ a w (fun k : K => k⁻¹) (fun _ => (1 : K))
    hw continuous_inv continuous_const Φ Ψ hΨ X
  simpa only [leftAverageInv_apply, map_inv, map_one, Subgroup.coe_inv, Subgroup.coe_one,
    Units.val_one, Matrix.mul_one] using h

/-- Jacquet's square zeta functional equation for compact matrix coefficients of complex
standard vectors, normalized by the corresponding reciprocal Gamma products. -/
def ComplexSquareCoefficientFunctionalEquationStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (κ : Measure K) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (a : ℂˣ) (ds : Fin Rank → ComplexCharacterData) (Φ : 𝓢(Mat, ℂ)) (f : G → ℂ)
    (w : K → ℂ), f ∈ complexStandardModule Rank (List.ofFn ds) → Continuous w →
    let F := compactCoefficient κ id w f
    let Fd (g : G) := F (inverseTranspose Rank ℂ g)
    ∃ (σ : ℝ) (N Nd : ℂ → ℂ), Differentiable ℂ N ∧ Differentiable ℂ Nd ∧
      (∀ s : ℂ, σ < s.re →
        Integrable (zetaKernel Φ F s) μ ∧
        Integrable (zetaKernel (matrixTransform a Φ) Fd s) μ ∧
        N s = (complexLFactor (List.ofFn ds)).denominator s * ∫ g, zetaKernel Φ F s g ∂μ ∧
        Nd s = (complexLFactor ((List.ofFn ds).map ComplexCharacterData.inv)).denominator s *
          ∫ g, zetaKernel (matrixTransform a Φ) Fd s g ∂μ) ∧
      ∀ s : ℂ, Nd (1 - s) =
        (complexEpsilon (List.ofFn ds) (-a) ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) * N s

/-- The same square functional equation with exponential growth on each vertical strip. -/
def ComplexSquareCoefficientFunctionalEquationGrowthStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (κ : Measure K) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (a : ℂˣ) (ds : Fin Rank → ComplexCharacterData) (Φ : 𝓢(Mat, ℂ)) (f : G → ℂ)
    (w : K → ℂ), f ∈ complexStandardModule Rank (List.ofFn ds) → Continuous w →
    let F := compactCoefficient κ id w f
    let Fd (g : G) := F (inverseTranspose Rank ℂ g)
    ∃ (σ : ℝ) (N Nd : ℂ → ℂ), Differentiable ℂ N ∧ Differentiable ℂ Nd ∧
      HasStripExponentialGrowth N ∧ HasStripExponentialGrowth Nd ∧
      (∀ s : ℂ, σ < s.re →
        Integrable (zetaKernel Φ F s) μ ∧
        Integrable (zetaKernel (matrixTransform a Φ) Fd s) μ ∧
        N s = (complexLFactor (List.ofFn ds)).denominator s * ∫ g, zetaKernel Φ F s g ∂μ ∧
        Nd s = (complexLFactor ((List.ofFn ds).map ComplexCharacterData.inv)).denominator s *
          ∫ g, zetaKernel (matrixTransform a Φ) Fd s g ∂μ) ∧
      ∀ s : ℂ, Nd (1 - s) =
        (complexEpsilon (List.ofFn ds) (-a) ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) * N s

theorem complexSquareCoefficientFunctionalEquationGrowth :
    ComplexSquareCoefficientFunctionalEquationGrowthStatement (r := r) := by
  intro μ _ κ _ _ a ds Φ f w hf hw
  let Ψ := leftAverageInv κ id continuous_id w hw Φ
  let Φd := matrixTransform a Φ
  let fd (g : G) := f (inverseTranspose Rank ℂ g)
  have hfd : Continuous fd := by
    have hc : Continuous (fun g : G => f (conjAut g)) := hf.1.continuous.comp continuous_conjAut
    simpa only [fd, inverseTranspose_eq_conjAut] using hc
  obtain ⟨R, N, Nd, hN, hNd, hNg, hNdg, hZ, hEq⟩ :=
    complexSquareStandardFunctionalEquationGrowth μ κ a ds Ψ f hf
  obtain ⟨M, hM⟩ := exists_height_bound_standard (Nat.succ_pos r) (List.ofFn ds) List.length_ofFn
  obtain ⟨C, hC, hbound⟩ := hM f hf
  have hboundd (g : G) : ‖fd g‖ ≤ C * complexMatrixHeight g ^ M := by
    simpa only [height_inverseTranspose] using hbound (inverseTranspose Rank ℂ g)
  let q := (((Rank : ℂ) - 1) / 2).re
  let σ := max R ((Rank : ℝ) + M + |q|)
  refine ⟨σ, N, Nd, hN, hNd, hNg, hNdg, ?_, hEq⟩
  intro s hs
  have hsZ := (le_max_left R ((Rank : ℝ) + M + |q|)).trans_lt hs
  have hsM : (Rank : ℝ) + M ≤ (s + ((Rank : ℂ) - 1) / 2).re := by
    rw [Complex.add_re]
    change (Rank : ℝ) + M ≤ s.re + q
    have ht := (le_max_right R ((Rank : ℝ) + M + |q|)).trans_lt hs
    linarith [neg_abs_le q]
  obtain ⟨_, _, hN₀, hNd₀⟩ := hZ s hsZ
  have hC₀ := complexSquareZetaCoefficientAverage μ κ id continuous_id w hw Φ f hf.1.continuous
    M C hC hbound s hsM
  have hCd := complexSquareZetaCoefficientAverage μ κ (conjK Rank) continuous_conjK w hw Φd fd hfd
    M C hC hboundd s hsM
  have he : matrixTransform a Ψ = leftAverageInv κ (conjK Rank) continuous_conjK w hw Φd :=
    matrixTransform_leftAverageInv κ a w hw Φ
  have hd : (fun g => compactCoefficient κ id w f (inverseTranspose Rank ℂ g)) =
      compactCoefficient κ (conjK Rank) w fd := dual_compactCoefficient κ w f
  change Nd s = (complexLFactor ((List.ofFn ds).map ComplexCharacterData.inv)).denominator s *
    ∫ g, zetaKernel (matrixTransform a Ψ) fd s g ∂μ at hNd₀
  rw [he, ← hCd.2, ← hd] at hNd₀
  exact ⟨hC₀.1, hd ▸ hCd.1, hN₀.trans (congrArg (_ * ·) hC₀.2.symm), hNd₀⟩


theorem complexSquareCoefficientFunctionalEquation :
    ComplexSquareCoefficientFunctionalEquationStatement (r := r) := by
  intro μ _ κ _ _ a ds Φ f w hf hw
  obtain ⟨σ, N, Nd, hN, hNd, _, _, hZ, hEq⟩ := complexSquareCoefficientFunctionalEquationGrowth μ κ a ds Φ f w hf hw
  exact ⟨σ, N, Nd, hN, hNd, hZ, hEq⟩

end Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta
