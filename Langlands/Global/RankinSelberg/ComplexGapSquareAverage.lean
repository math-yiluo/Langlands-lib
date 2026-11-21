import Langlands.Global.RankinSelberg.ComplexSquareZetaCoefficientAverage
import Langlands.Global.RankinSelberg.ComplexGodementSchwartz
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerRegularity
import Langlands.Representation.Archimedean.ComplexStandardDeterminantTwist

/-! # Determinant-twisted compact averages of the leading square test -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapSquareAverage

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexDeterminantTwist (detCharacter detCharacter_mul detCharacter_inv_mul)
open Langlands.GeneralLinear (determinant determinantContinuous inverseTranspose continuous_inverseTranspose)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexCharacterChange (complexMatrixHeight_mul_le)
open ComplexGodement (characterWeight normPower norm_characterWeight)
open ComplexPlaceAnalytic (two_le_complexMatrixHeight exists_norm_det_rpow_le_complexMatrixHeight)
open ComplexSquareZeta (compactCoefficient zetaKernel leftAverageInv leftAverageInv_apply
  complexSquareZetaCoefficientAverage)
open ArchimedeanLocal (complexNormalizedAbs)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel

variable {t : ℕ}
local notation "k" => t + 1
local notation "H" => Langlands.GeneralLinear (t + 1) ℂ
local notation "K" => unitaryCompact ℂ (t + 1)
local notation "M" => Matrix (Fin (t + 1)) (Fin (t + 1)) ℂ
local notation "ι" => inverseTranspose (t + 1) ℂ

/-- The square zeta kernel written with the character of the adjoining column. -/
def squareKernel (d : ComplexCharacterData) (Φ : M → ℂ) (f : H → ℂ) (s : ℂ) (g : H) : ℂ :=
  Φ g.val * characterWeight d ((t : ℂ) / 2 + s) (determinant g) * f g

theorem squareKernel_eq_zetaKernel (d : ComplexCharacterData) (Φ : M → ℂ) (f : H → ℂ)
    (s : ℂ) (g : H) : squareKernel d Φ f s g =
      zetaKernel Φ (fun x => detCharacter d.character x * f x) s g := by
  unfold squareKernel zetaKernel detCharacter
  change Φ g.val * ((d.character (determinant g) : ℂ) * normPower ((t : ℂ) / 2 + s) (determinant g)) * f g = _
  rw [show s + (((t + 1 : ℕ) : ℂ) - 1) / 2 = (t : ℂ) / 2 + s by push_cast; ring]
  ring

private theorem detCharacter_height_bound (d : ComplexCharacterData) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ g : H, ‖detCharacter d.character g‖ ≤ C * complexMatrixHeight g ^ N := by
  obtain ⟨C, N, hC, hg⟩ := exists_norm_det_rpow_le_complexMatrixHeight (Nat.succ_pos t) (2 * d.exponent.re)
  refine ⟨C, N, hC, fun g => ?_⟩
  have h0 : characterWeight d 0 (determinant g) = detCharacter d.character g := by
    change (d.character (determinant g) : ℂ) * (Langlands.Archimedean.ComplexMaximalParabolicIntegration.normSqC
      (determinant g : ℂ)) ^ (0 : ℂ) = _
    rw [Complex.cpow_zero, mul_one]
    rfl
  rw [← h0, norm_characterWeight, add_zero]
  change (‖g.val.det‖ ^ (2 : ℕ)) ^ d.exponent.re ≤ _
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  exact hg g

/-- The Whittaker matrix coefficient at a fixed evaluation point satisfies a polynomial bound. -/
theorem whittakerLeftTranslate_bound {es : List ComplexCharacterData} {a : ℂˣ}
    {V : H → ℂ} (hV : V ∈ complexWhittakerModel t es a) (x : H) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ g : H, ‖V (x * g)‖ ≤ C * complexMatrixHeight g ^ N := by
  obtain ⟨C, N, hC, hW⟩ := complexWhittakerModel_moderateGrowth hV
  have h₁ (g : H) : 1 ≤ complexMatrixHeight g :=
    (by norm_num : (1 : ℝ) ≤ 2).trans (two_le_complexMatrixHeight (Nat.succ_pos t) g)
  refine ⟨C * complexMatrixHeight x ^ N, N, mul_nonneg hC (pow_nonneg (zero_le_one.trans (h₁ x)) _), fun g => (hW (x * g)).trans ?_⟩
  rw [max_eq_right (h₁ _), mul_assoc, ← mul_pow]
  apply mul_le_mul_of_nonneg_left _ hC
  exact pow_le_pow_left₀ (zero_le_one.trans (h₁ _)) (complexMatrixHeight_mul_le x g) _

/-- A reproducing compact average of the square test moves to the function with the determinant twist. -/
theorem squareKernel_average (ν : Measure H) [ν.IsHaarMeasure] (κ : Measure K) [IsFiniteMeasure κ]
    (u : K → K) (hu : Continuous u) (w : K → ℂ) (hw : Continuous w)
    (d : ComplexCharacterData) (Φ : 𝓢(M, ℂ)) (f : H → ℂ) (hf : Continuous f)
    (hfB : ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ g, ‖f g‖ ≤ C * complexMatrixHeight g ^ N)
    (hRec : ∀ X, (∫ j, w j * (d.character ((determinant (u j).val)⁻¹) : ℂ) *
      Φ ((u j).val⁻¹.val * X) ∂κ) = Φ X) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (squareKernel d Φ f s) ν ∧
      (∫ g, squareKernel d Φ f s g ∂ν) = ∫ g, squareKernel d Φ (compactCoefficient κ u w f) s g ∂ν := by
  let F (g : H) := detCharacter d.character g * f g
  let w' (j : K) := w j * detCharacter d.character⁻¹ (u j).val
  have hF : Continuous F :=
    (Langlands.Archimedean.ComplexDeterminantTwist.contMDiff_detCharacter d.character).continuous.mul hf
  have hw' : Continuous w' := hw.mul
    (((Langlands.Archimedean.ComplexDeterminantTwist.contMDiff_detCharacter d.character⁻¹).continuous.comp
      continuous_subtype_val).comp hu)
  obtain ⟨C, N, hC, hB⟩ := hfB
  obtain ⟨D, J, hD, hχ⟩ := detCharacter_height_bound (t := t) d
  have hb (g : H) : ‖F g‖ ≤ (D * C) * complexMatrixHeight g ^ (J + N) := by
    rw [show ‖F g‖ = ‖detCharacter d.character g‖ * ‖f g‖ from norm_mul _ _, pow_add]
    exact (mul_le_mul (hχ g) (hB g) (norm_nonneg _)
      (mul_nonneg hD (pow_nonneg (zero_le_two.trans (two_le_complexMatrixHeight (Nat.succ_pos t) g)) _))).trans_eq (by ring)
  have hΨ : leftAverageInv κ u hu w' hw' Φ = Φ := by
    ext X
    rw [leftAverageInv_apply, ← hRec X]
    refine integral_congr_ae (ae_of_all _ fun j => ?_)
    dsimp only [w']
    rw [Langlands.Archimedean.ComplexDeterminantTwist.detCharacter_inv, detCharacter,
      map_inv, Units.val_inv_eq_inv_val]
  have hCoeff (g : H) : compactCoefficient κ u w' F g =
      detCharacter d.character g * compactCoefficient κ u w f g := by
    unfold compactCoefficient
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun j => ?_)
    dsimp only [F, w']
    rw [detCharacter_mul]
    calc
      _ = (detCharacter d.character⁻¹ (u j).val * detCharacter d.character (u j).val) *
          (detCharacter d.character g * (w j * f ((u j).val * g))) := by ring
      _ = _ := by rw [detCharacter_inv_mul, one_mul]
  let σ : ℝ := (t.succ : ℝ) + (J + N : ℕ) + 1
  refine ⟨σ, fun s hs => ?_⟩
  have hs' : (t.succ : ℝ) + (J + N : ℕ) ≤ (s + (((t.succ : ℕ) : ℂ) - 1) / 2).re := by
    have ht : 0 ≤ (t : ℝ) := Nat.cast_nonneg _
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.sub_re, Complex.one_re, Complex.natCast_re,
      Nat.cast_succ] at *
    dsimp only [σ] at hs
    rw [Nat.cast_succ] at hs
    linarith only [hs, ht]
  have hRaw := complexSquareZetaCoefficientAverage ν (Measure.dirac (1 : K)) (fun _ => 1)
    continuous_const (fun _ => 1) continuous_const Φ F hF (J + N) (D * C) (mul_nonneg hD hC) hb s hs'
  have hRawCoeff : compactCoefficient (Measure.dirac (1 : K)) (fun _ => 1) (fun _ => 1) F = F := by
    funext g
    simp only [compactCoefficient, Subgroup.coe_one, one_mul, integral_dirac]
  rw [hRawCoeff] at hRaw
  have hAvg := complexSquareZetaCoefficientAverage ν κ u hu w' hw' Φ F hF (J + N)
    (D * C) (mul_nonneg hD hC) hb s hs'
  rw [hΨ, funext hCoeff] at hAvg
  refine ⟨?_, ?_⟩
  · rw [funext (squareKernel_eq_zetaKernel d Φ f s)]
    exact hRaw.1
  · simp only [squareKernel_eq_zetaKernel]
    exact hAvg.2.symm

end Langlands.Global.RankinSelbergGlobal.ComplexGapSquareAverage
