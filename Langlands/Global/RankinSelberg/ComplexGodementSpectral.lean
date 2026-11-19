import Langlands.Global.RankinSelberg.ComplexGodementCompact
import Langlands.Global.RankinSelberg.UnequalAnalyticHolomorphy
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Spectral shifts of compact complex Godement sections -/

noncomputable section

open MeasureTheory Measure
open scoped Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance spectralGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℂ) :=
  borel _
local instance spectralGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩
private abbrev Rect (m : ℕ) := Matrix (Fin m) (Fin (m + 1)) ℂ

private def logAbsDet {m : ℕ} (g : Langlands.GeneralLinear m ℂ) : ℝ :=
  Real.log (‖(determinant g : ℂ)‖ ^ 2)

private theorem continuous_logAbsDet (m : ℕ) : Continuous (logAbsDet (m := m)) := by
  have hnorm : Continuous (fun h : Langlands.GeneralLinear m ℂ => ‖(determinant h : ℂ)‖ ^ 2) :=
    (Units.continuous_val.comp determinantContinuous.continuous).norm.pow 2
  exact hnorm.log fun h => pow_ne_zero _ (norm_ne_zero_iff.mpr (determinant h).ne_zero)

private theorem integrable_expMoments_of_compactSupport {X : Type*} [TopologicalSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] {ν : Measure X}
    [IsLocallyFiniteMeasure ν] {A : X → ℂ} {L : X → ℝ} (hA : Continuous A)
    (hL : Continuous L) (hAc : HasCompactSupport A) (s : ℝ) :
    Integrable (fun h => ‖A h‖ * Real.exp (s * L h)) ν := by
  have hc : Continuous (fun h => ‖A h‖ * Real.exp (s * L h)) :=
    hA.norm.mul (Real.continuous_exp.comp (continuous_const.mul hL))
  refine hc.integrable_of_hasCompactSupport (HasCompactSupport.of_support_subset_isCompact hAc ?_)
  intro h hh
  apply subset_tsupport A
  intro hz
  apply hh
  change ‖A h‖ * Real.exp (s * L h) = 0
  rw [hz, norm_zero, zero_mul]

/-- Vary the spectral exponent of the added character by `s`. -/
def godementSectionShift {m : ℕ} (ν : Measure (Langlands.GeneralLinear m ℂ))
    (d : ComplexCharacterData) (Φ : Rect m → ℂ) (f : Langlands.GeneralLinear m ℂ → ℂ)
    (g : Langlands.GeneralLinear (m + 1) ℂ) (s : ℂ) : ℂ :=
  (characterWeight d ((m : ℂ) / 2) (determinant g) * Complex.exp (s * logAbsDet g)) *
    ∫ h, godementSectionIntegrand d Φ f g h * Complex.exp (s * logAbsDet h) ∂ν

@[simp]
theorem godementSectionShift_zero {m : ℕ} (ν : Measure (Langlands.GeneralLinear m ℂ))
    (d : ComplexCharacterData) (Φ : Rect m → ℂ) (f : Langlands.GeneralLinear m ℂ → ℂ)
    (g : Langlands.GeneralLinear (m + 1) ℂ) :
    godementSectionShift ν d Φ f g 0 = godementSection ν d Φ f g := by
  simp [godementSectionShift, godementSection]

set_option backward.isDefEq.respectTransparency true in
/-- For compact tests supported in the full-row-rank locus the shifted section is entire in
the added spectral exponent, at each fixed larger group element. -/
theorem differentiable_godementSectionShift {m : ℕ}
    (ν : Measure (Langlands.GeneralLinear m ℂ)) [IsLocallyFiniteMeasure ν]
    (d : ComplexCharacterData) {Φ : Rect m → ℂ} (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) (hfull : ∀ X ∈ tsupport Φ, HasFullRowRank X)
    {f : Langlands.GeneralLinear m ℂ → ℂ} (hf : Continuous f)
    (g : Langlands.GeneralLinear (m + 1) ℂ) :
    Differentiable ℂ (godementSectionShift (m := m) ν d Φ f g) := by
  let A : Langlands.GeneralLinear m ℂ → ℂ := godementSectionIntegrand d Φ f g
  let L := logAbsDet (m := m)
  have hpair : Continuous (fun h : Langlands.GeneralLinear m ℂ => (g, h)) :=
    continuous_const.prodMk continuous_id
  have hA := (continuous_godementSectionIntegrand (m := m) d (Φ := Φ) hΦ (f := f) hf).comp hpair
  change Continuous A at hA
  have hL : Continuous L := continuous_logAbsDet m
  have hAc : HasCompactSupport A :=
    hasCompactSupport_godementSectionIntegrand (m := m) d (Φ := Φ) hΦc hfull f g
  have hI : Differentiable ℂ (fun s : ℂ => ∫ h, A h * Complex.exp (s * L h) ∂ν) :=
    UnequalAnalytic.differentiable_integral_mul_cexp hA.aestronglyMeasurable hL.aestronglyMeasurable
      (integrable_expMoments_of_compactSupport hA hL hAc)
  have hE : Differentiable ℂ (fun s : ℂ => Complex.exp (s * logAbsDet g)) :=
    (differentiable_id.mul_const (logAbsDet g : ℂ)).cexp
  have hC : Differentiable ℂ (fun _ : ℂ => characterWeight d ((m : ℂ) / 2) (determinant g)) :=
    differentiable_const _
  exact (hC.mul hE).mul hI

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
