import Langlands.Global.RankinSelberg.ComplexGodementGaussianApproximation
import Langlands.Global.RankinSelberg.ComplexGodementStandardGrowth

/-! # Uniform approximation of the compact values of Godement sections -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open ComplexGodementGaussianPolynomial (Coordinates gaussianPolynomial matrixGaussian
  matrixGaussian_mul_unitary complexGodementGaussianApproximation exists_gaussianPolynomial_dilation)

local instance uniformApproximationGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance uniformApproximationGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩

variable {m : ℕ}
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear (m + 1) ℂ
local notation "Kc" => unitaryCompact ℂ (m + 1)
local notation "Mat" => Matrix (Fin m) (Fin (m + 1)) ℂ
local notation "ν" => complexGeneralLinearHaar m

private theorem matrixGaussian_unitary_trailingRows (h : H) (k : Kc) :
    matrixGaussian (h.val * trailingRows k.val.val) =
      matrixGaussian (h.val * trailingRows (1 : G).val) := by
  have hRows : trailingRows k.val.val = trailingRows (1 : G).val * k.val.val := by
    simpa only [trailingRows, Units.val_one, Matrix.one_mul, Matrix.submatrix_id_id] using
      (Matrix.submatrix_mul (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
        k.val.val Fin.succ id id Function.bijective_id)
  rw [hRows, ← Matrix.mul_assoc, matrixGaussian_mul_unitary]

private theorem godementSection_sum {l : ℕ} (d : ComplexCharacterData)
    (f : H → ℂ) (Φ : Fin l → 𝓢(Mat, ℂ)) (g : G)
    (hI : ∀ j, Integrable (godementSectionIntegrand d (Φ j) f g) ν) :
    godementSection ν d (∑ j, Φ j) f g = ∑ j, godementSection ν d (Φ j) f g := by
  have hsum : godementSectionIntegrand d (∑ j, Φ j) f g =
      fun h => ∑ j, godementSectionIntegrand d (Φ j) f g h := by
    funext h
    simp only [godementSectionIntegrand, Finset.sum_apply, Finset.sum_mul]
  simp only [godementSection, hsum, integral_finsetSum Finset.univ (fun j _ => hI j), Finset.mul_sum]

/-- In the Godement convergence region, the compact restriction of a section of a
compactly supported Schwartz test is uniformly approximated by a finite sum of
Godement sections of dilated Gaussian-polynomial tests, with the smaller vector fixed. -/
def ComplexGodementUniformApproximationStatement : Prop :=
  0 < m → ∀ (ds : List ComplexCharacterData), ds.length = m →
    ∃ M : ℕ, ∀ (d : ComplexCharacterData) (f : H → ℂ), f ∈ complexStandardModule m ds →
      (m : ℝ) + M ≤ (d.exponent + ((m : ℂ) + 1) / 2).re →
      ∀ (Φ : 𝓢(Mat, ℂ)), HasCompactSupport Φ → ∀ ε : ℝ, 0 < ε →
        ∃ (l : ℕ) (z : Fin l → ℂˣ) (p : Fin l → MvPolynomial (Coordinates m (m + 1)) ℂ),
          ∀ k : Kc, ‖godementSection ν d Φ f k.val -
            ∑ j, godementSection ν d
              (fun X => gaussianPolynomial (p j) ((z j : ℂ) • X)) f k.val‖ ≤ ε

theorem complexGodementUniformApproximation : ComplexGodementUniformApproximationStatement (m := m) := by
  intro hm ds hds
  obtain ⟨M, hM⟩ := complexGodementStandardConvergence m hm ds hds
  refine ⟨M, fun d f hf hσ Φ hΦ ε hε => ?_⟩
  let Γ := gaussianPolynomial (1 : MvPolynomial (Coordinates m (m + 1)) ℂ)
  have hΓ (X : Mat) : Γ X = matrixGaussian X := by simp [Γ]
  let v := fun h : H => ‖godementSectionIntegrand d Γ f 1 h‖
  have hv : Integrable v ν := (hM d Γ f hf hσ 1).norm
  let C := ∫ h, v h ∂ν
  have hC : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  let b (k : Kc) := ‖characterWeight d ((m : ℂ) / 2) (determinant k.val)‖
  let : CompactSpace Kc := ComplexDuality.compactSpace_unitaryCompact (m + 1)
  have hb : Continuous b :=
    ((continuous_characterWeight d ((m : ℂ) / 2)).comp
      (determinantContinuous.continuous.comp continuous_subtype_val)).norm
  obtain ⟨B₀, hB₀⟩ := (isCompact_range hb).bddAbove
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hB' (k : Kc) : b k ≤ B :=
    (hB₀ (Set.mem_range_self k)).trans (le_max_left _ _)
  let δ := ε / (B * C + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨l, e, q, hApprox⟩ := complexGodementGaussianApproximation m (m + 1)
    Φ Φ.continuous hΦ δ hδ
  choose z p hp using fun j => exists_gaussianPolynomial_dilation (q j) (e j)
  let Ψ (j : Fin l) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((ContinuousLinearEquiv.smulLeft (R₁ := ℂ) (M₁ := Mat) (z j)).restrictScalars ℝ)
    (gaussianPolynomial (p j))
  have hΨ (j : Fin l) (X : Mat) : Ψ j X = gaussianPolynomial (p j) ((z j : ℂ) • X) := rfl
  let T := ∑ j, Ψ j
  have hT (X : Mat) : ‖Φ X - T X‖ ≤ δ * ‖matrixGaussian X‖ := by
    simpa only [T, sum_apply, hΨ, hp] using hApprox X
  refine ⟨l, z, p, fun k => ?_⟩
  change ‖godementSection ν d Φ f k.val - ∑ j, godementSection ν d (Ψ j) f k.val‖ ≤ ε
  rw [← godementSection_sum d f Ψ k.val (fun j => hM d (Ψ j) f hf hσ k.val)]
  have hTfun : (∑ j, (Ψ j : Mat → ℂ)) = (T : Mat → ℂ) := by
    funext X
    simp only [T, Finset.sum_apply, sum_apply]
  rw [hTfun]
  change ‖godementSection ν d Φ f k.val - godementSection ν d T f k.val‖ ≤ ε
  let I := godementSectionIntegrand d Φ f k.val
  let J := godementSectionIntegrand d T f k.val
  have hI : Integrable I ν := hM d Φ f hf hσ k.val
  have hJ : Integrable J ν := hM d T f hf hσ k.val
  have hdiff (h : H) : ‖I h - J h‖ ≤ δ * v h := by
    let X : Mat := h.val * trailingRows k.val.val
    let α := f h⁻¹
    let β := characterWeight d (((m : ℂ) + 1) / 2) (determinant h)
    change ‖Φ X * α * β - T X * α * β‖ ≤ _
    rw [← sub_mul, ← sub_mul, norm_mul, norm_mul]
    calc
      _ ≤ (δ * ‖matrixGaussian X‖) * ‖α‖ * ‖β‖ := by gcongr; exact hT X
      _ = _ := by
        dsimp only [X, v, godementSectionIntegrand]
        rw [matrixGaussian_unitary_trailingRows, hΓ, norm_mul, norm_mul]
        ring
  have hBound : (∫ h, ‖I h - J h‖ ∂ν) ≤ δ * C := by
    rw [← integral_const_mul]
    exact integral_mono ((hI.sub hJ).norm) (hv.const_mul δ) hdiff
  let a := characterWeight d ((m : ℂ) / 2) (determinant k.val)
  have hε' : b k * (δ * C) ≤ ε := by
    calc
      _ ≤ B * (δ * C) := mul_le_mul_of_nonneg_right (hB' k) (by positivity)
      _ = ε * ((B * C) / (B * C + 1)) := by dsimp only [δ]; ring
      _ ≤ ε := by
        have hpos : 0 < B * C + 1 := by positivity
        have hle : B * C / (B * C + 1) ≤ 1 := (div_le_one hpos).mpr (by linarith)
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hle hε.le
  change ‖a * (∫ h, I h ∂ν) - a * (∫ h, J h ∂ν)‖ ≤ ε
  rw [← mul_sub, ← integral_sub hI hJ, norm_mul]
  calc
    _ ≤ b k * ∫ h, ‖I h - J h‖ ∂ν :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ ≤ b k * (δ * C) := mul_le_mul_of_nonneg_left hBound (norm_nonneg _)
    _ ≤ ε := hε'

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
