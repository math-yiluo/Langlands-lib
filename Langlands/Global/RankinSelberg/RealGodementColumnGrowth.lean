import Langlands.Global.RankinSelberg.RealGodementSmoothLeading
import Langlands.Global.RankinSelberg.RealGodementTranslatedSeminorm
import Langlands.Global.RankinSelberg.RealEqualDualConvergence

/-! # Common polynomial growth of real Godement column values -/

noncomputable section

universe u

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open RealJacquetFrobenius RealPlaceRestriction

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

private theorem norm_determinantWeight_charData {n : ℕ} (p : Fin 2) (w s : ℂ)
    (g : Langlands.GeneralLinear n ℝ) :
    ‖determinantWeight (charData p w) s g‖ = |g.val.det| ^ (w + s).re := by
  let d := determinant g
  have hPos : 0 < |(d : ℝ)| := abs_pos.mpr d.ne_zero
  change ‖((charData p w).character d : ℂ) * ((|(d : ℝ)| : ℝ) : ℂ) ^ s‖ = |(d : ℝ)| ^ (w + s).re
  rw [(charData p w).character_eq]
  simp only [charData, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_abs,
    div_self hPos.ne', one_pow, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hPos]
  rw [← Real.rpow_add hPos, Complex.add_re]

/-- A single upper group growth exponent works for every test and every lower coefficient
whose regular right derivatives share the given lower group growth exponent. -/
def RealGodementColumnGrowthStatement : Prop :=
  ∀ (t : ℕ) (D : RealQuotientMeasureData t) (a : ℝˣ) (p : Fin 2) (w : ℂ) (N : ℕ),
    ∃ M : ℕ, ∀ (W : Langlands.GeneralLinear (t + 1) ℝ → ℂ),
      (∀ Xs, RealLocalWhittaker.iteratedRightDerivative t Xs W ∈
        RealLocalWhittaker.regularFunctions t (-a)) →
      (∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
        ‖RealLocalWhittaker.iteratedRightDerivative t Xs W g‖ ≤ C * realMatrixHeight g ^ N) →
      ∀ (Φ : 𝓢(Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ, ℂ)),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
        ‖godementLeadingFamily D a Φ W p g w‖ ≤ C * realMatrixHeight g ^ M

/-- A lower family with shared constants and bounded leading exponents admits one upper
polynomial growth bound for each fixed Schwartz test. -/
def RealGodementColumnFamilyGrowthStatement : Prop :=
  ∀ (ι : Type u) (t : ℕ) (D : RealQuotientMeasureData t) (a : ℝˣ) (p : Fin 2)
    (T : ℝ), 0 ≤ T → ∀ N : ℕ, ∃ M : ℕ,
      ∀ (W : ι → Langlands.GeneralLinear (t + 1) ℝ → ℂ),
        (∀ j Xs, RealLocalWhittaker.iteratedRightDerivative t Xs (W j) ∈
          RealLocalWhittaker.regularFunctions t (-a)) →
        (∀ Xs, ∃ C : ℝ, 0 ≤ C ∧ ∀ j g,
          ‖RealLocalWhittaker.iteratedRightDerivative t Xs (W j) g‖ ≤ C * realMatrixHeight g ^ N) →
        ∀ (w : ι → ℂ), (∀ j, ‖w j‖ ≤ T) →
        ∀ (Φ : 𝓢(Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ, ℂ)),
        ∃ C : ℝ, 0 ≤ C ∧ ∀ j g,
          ‖godementLeadingFamily D a Φ (W j) p g (w j)‖ ≤ C * realMatrixHeight g ^ M

theorem realGodementColumnFamilyGrowth : RealGodementColumnFamilyGrowthStatement.{u} := by
  intro ι t D a p T hT N
  let μ := D.groupHaar
  let : μ.IsHaarMeasure := D.groupHaar_isHaar
  let S := (((t : ℂ) + 1) / 2)
  let v := (t : ℂ) / 2
  let R := T + |v.re - (t + 1 : ℕ)|
  obtain ⟨q, hq, hBounds⟩ := exists_columnMellin_family_seminorm (ι := ι) μ a N R
    (add_nonneg hT (abs_nonneg _))
  have hRank : 0 < t + 2 := by omega
  obtain ⟨I, L, A, hA, hQ⟩ := realGodementTranslatedSeminorm (t + 1) (t + 2) hRank q hq
  obtain ⟨C, K, hC, hD⟩ := exists_det_rpow_le_realMatrixHeight_of_abs_le hRank (T + |S.re|)
  refine ⟨K + L, fun W hReg hGrowth w hw Φ => ?_⟩
  let s (j : ι) := w j + v
  have hRe (j : ι) : |(w j).re| ≤ T := (Complex.abs_re_le_norm _).trans (hw j)
  have hStrip (j : ι) : |(s j).re - (t + 1 : ℕ)| ≤ R := by
    rw [show (s j).re - (t + 1 : ℕ) = (w j).re + (v.re - (t + 1 : ℕ)) by
      simp only [s, Complex.add_re]; ring]
    exact (abs_add_le _ _).trans (add_le_add_left (hRe j) _)
  have hDetBound (j : ι) : |(w j + S).re| ≤ T + |S.re| := by
    rw [Complex.add_re]
    exact (abs_add_le _ _).trans (add_le_add_left (hRe j) _)
  obtain ⟨B, hB, hB₀, hPoint⟩ := hBounds W hReg hGrowth
  let b := ∫ h, B h ∂μ
  let P := I.sup (schwartzSeminormFamily ℝ (Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ) ℂ) Φ
  have hb : 0 ≤ b := integral_nonneg hB₀
  have hP : 0 ≤ P := apply_nonneg _ _
  refine ⟨C * (A * P * b), by positivity, fun j g => ?_⟩
  let e := weylLong (t + 2) ℝ * g
  let Ψ := rectangularTranslate 1 e Φ
  let F := columnMellinIntegrand a Ψ (W j) p.val (s j)
  have hG : RealUniformWhittaker.HasUniformDerivativeGrowth (W j) := by
    refine ⟨N, fun Xs => ?_⟩
    obtain ⟨C, hC, h⟩ := hGrowth Xs
    exact ⟨C, hC, h j⟩
  have hFi : Integrable F μ := (realGodementColumnConvergence t μ a Ψ (W j) (hReg j) hG p.val).1 (s j)
  have hF : ‖∫ h, F h ∂μ‖ ≤ q Ψ * b := by
    calc
      _ ≤ ∫ h, ‖F h‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ h, q Ψ * B h ∂μ := integral_mono hFi.norm (hB.const_mul _) (hPoint j Ψ p.val (s j) (hStrip j))
      _ = _ := integral_const_mul _ _
  have hHeight : realMatrixHeight e = realMatrixHeight g :=
    RealPrincipalSeries.realMatrixHeight_unitary_mul (RealEqualDualConvergence.weylLong_mem_unitary (r := t + 1)) g
  have hDet : ‖determinantWeight (charData p (w j)) S e‖ ≤ C * realMatrixHeight g ^ K := by
    rw [norm_determinantWeight_charData, ← hHeight]
    exact hD _ (hDetBound j) e
  have hTest : q Ψ ≤ A * realMatrixHeight g ^ L * P := by
    rw [← hHeight]
    exact hQ e Φ
  have hH : 0 ≤ realMatrixHeight g := realMatrixHeight_nonneg g
  change ‖determinantWeight (charData p (w j)) S e * (∫ h, F h ∂μ)‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ (C * realMatrixHeight g ^ K) * (q Ψ * b) :=
      mul_le_mul hDet hF (norm_nonneg _) (by positivity)
    _ ≤ (C * realMatrixHeight g ^ K) * ((A * realMatrixHeight g ^ L * P) * b) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hTest hb) (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem realGodementColumnGrowth : RealGodementColumnGrowthStatement := by
  intro t D a p w N
  obtain ⟨M, hM⟩ := realGodementColumnFamilyGrowth Unit t D a p ‖w‖ (norm_nonneg _) N
  refine ⟨M, fun W hReg hGrowth Φ => ?_⟩
  obtain ⟨C, hC, h⟩ := hM (fun _ => W) (fun _ => hReg)
    (fun Xs => by obtain ⟨C, hC, h⟩ := hGrowth Xs; exact ⟨C, hC, fun _ => h⟩)
    (fun _ => w) (fun _ => le_rfl) Φ
  exact ⟨C, hC, h ()⟩

end Langlands.Global.RankinSelbergGlobal.RealGodement
