import Langlands.Global.RankinSelberg.ComplexGodementStandardGrowth
import Langlands.Global.RankinSelberg.ComplexGodementSpectral
import Langlands.Analysis.MellinHalfPlaneProof
import Langlands.Representation.Archimedean.ComplexJacquetBorel

/-! # Holomorphy of the complex Godement section on its convergence half-plane -/

noncomputable section

open MeasureTheory
open scoped SchwartzMap ContDiff Manifold Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.GeneralLinear Langlands.Archimedean Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open ArchimedeanLocal (complexNormalizedAbs)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance halfPlaneGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℂ) :=
  borel _
local instance halfPlaneGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩

private abbrev Rect (m : ℕ) := Matrix (Fin m) (Fin (m + 1)) ℂ

/-- Increase the exponent of the complex character by `s`, keeping its angular weight. -/
def shiftedCharacter (d : ComplexCharacterData) (s : ℂ) : ComplexCharacterData :=
  characterOfParams d.weight (d.exponent + s)

@[simp]
theorem shiftedCharacter_exponent (d : ComplexCharacterData) (s : ℂ) :
    (shiftedCharacter d s).exponent = d.exponent + s := rfl

private theorem normPower_eq_exp (z : ℂˣ) (s : ℂ) :
    normPower s z = Complex.exp (s * (Real.log (complexNormalizedAbs (z : ℂ)) : ℂ)) := by
  change ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s = _
  have hnorm : 0 < ‖(z : ℂ)‖ ^ 2 := pow_pos (norm_pos_iff.mpr z.ne_zero) _
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hnorm.ne'),
    ← Complex.ofReal_log hnorm.le, mul_comm]
  rfl

private theorem characterWeight_shifted (d : ComplexCharacterData) (s u : ℂ) (z : ℂˣ) :
    characterWeight (shiftedCharacter d s) u z = characterWeight d u z * normPower s z := by
  have hpos : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  have hne : (‖(z : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hnorm : normPower s z = (‖(z : ℂ)‖ : ℂ) ^ (2 * s) := by
    change ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s = _
    rw [pow_two, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hpos.le hpos.le,
      ← Complex.cpow_add _ _ hne]
    congr 1
    ring
  change ((shiftedCharacter d s).character z : ℂ) * normPower u z =
    (d.character z : ℂ) * normPower u z * normPower s z
  rw [(shiftedCharacter d s).character_eq, d.character_eq, hnorm]
  change ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ d.weight *
      (‖(z : ℂ)‖ : ℂ) ^ (2 * (d.exponent + s)) * normPower u z = _
  rw [mul_add, Complex.cpow_add _ _ hne]
  ring

private theorem godementSectionIntegrand_shifted {m : ℕ} (d : ComplexCharacterData) (s : ℂ)
    (Φ : Rect m → ℂ) (f : Langlands.GeneralLinear m ℂ → ℂ)
    (g : Langlands.GeneralLinear (m + 1) ℂ) (h : Langlands.GeneralLinear m ℂ) :
    godementSectionIntegrand (shiftedCharacter d s) Φ f g h =
      godementSectionIntegrand d Φ f g h * normPower s (determinant h) := by
  unfold godementSectionIntegrand
  rw [characterWeight_shifted, ← mul_assoc]

/-- The exponential shift already used for Godement sections is exactly the section with its
added character shifted. -/
theorem godementSectionShift_eq_section {m : ℕ} (ν : Measure (Langlands.GeneralLinear m ℂ))
    (d : ComplexCharacterData) (Φ : Rect m → ℂ) (f : Langlands.GeneralLinear m ℂ → ℂ)
    (g : Langlands.GeneralLinear (m + 1) ℂ) (s : ℂ) :
    godementSectionShift ν d Φ f g s = godementSection ν (shiftedCharacter d s) Φ f g := by
  change (characterWeight d ((m : ℂ) / 2) (determinant g) *
    Complex.exp (s * (Real.log (complexNormalizedAbs (determinant g : ℂ)) : ℂ))) *
    (∫ h, godementSectionIntegrand d Φ f g h *
      Complex.exp (s * (Real.log (complexNormalizedAbs (determinant h : ℂ)) : ℂ)) ∂ν) = _
  simp only [godementSection, characterWeight_shifted, godementSectionIntegrand_shifted,
    normPower_eq_exp]

/-- Complex-power integration is holomorphic on any right half-plane where the real moments
are integrable. This translates the published positive-half-plane Mellin theorem. -/
private theorem differentiableOn_mellin_right {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {A : X → ℂ} {D : X → ℝ} (hA : AEStronglyMeasurable A ν)
    (hD : AEMeasurable D ν) (hpos : ∀ x, 0 < D x) {b : ℝ}
    (hI : ∀ r : ℝ, b < r → Integrable (fun x => A x * (D x : ℂ) ^ (r : ℂ)) ν) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ x, A x * (D x : ℂ) ^ s ∂ν) {s : ℂ | b < s.re} := by
  have hm := Langlands.Analysis.mellinHalfPlane X ν A D (-b) hpos hA hD (fun r hr => by
    have h := hI (r + b) (by linarith)
    simpa only [Complex.ofReal_neg, sub_neg_eq_add, Complex.ofReal_add] using h)
  have h_aff : Differentiable ℂ (fun s : ℂ => s - (b : ℂ)) := differentiable_id.sub_const _
  have hmaps : Set.MapsTo (fun s : ℂ => s - (b : ℂ)) {s : ℂ | b < s.re}
      {s : ℂ | 0 < s.re} := by
    intro z hz
    change 0 < (z - (b : ℂ)).re
    change b < z.re at hz
    simpa only [Complex.sub_re, Complex.ofReal_re, sub_pos] using hz
  have hc := hm.comp h_aff.differentiableOn hmaps
  simpa only [Function.comp_def, Complex.ofReal_neg, sub_neg_eq_add, sub_add_cancel] using hc

/-- For each fixed standard module, the normalized parameter shift of a Schwartz Godement
section is holomorphic wherever the real part of the added exponent exceeds a common bound. -/
def ComplexGodementHalfPlaneStatement : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ (ds : List ComplexCharacterData), ds.length = m →
    ∃ B : ℝ, ∀ (d : ComplexCharacterData) (Φ : 𝓢(Rect m, ℂ))
      (f : Langlands.GeneralLinear m ℂ → ℂ), f ∈ complexStandardModule m ds →
      ∀ g : Langlands.GeneralLinear (m + 1) ℂ,
        DifferentiableOn ℂ (godementSectionShift (complexGeneralLinearHaar m) d Φ f g)
          {s : ℂ | B < d.exponent.re + s.re}

theorem complexGodementHalfPlane : ComplexGodementHalfPlaneStatement := by
  intro m hm ds hds
  obtain ⟨M, hM⟩ := complexGodementStandardConvergence m hm ds hds
  let B : ℝ := (m : ℝ) + M - (((m : ℂ) + 1) / 2).re
  refine ⟨B, fun d Φ f hf g => ?_⟩
  let b := B - d.exponent.re
  let D (h : Langlands.GeneralLinear m ℂ) := complexNormalizedAbs (determinant h : ℂ)
  let A := godementSectionIntegrand d Φ f g
  have hpair : Continuous (fun h : Langlands.GeneralLinear m ℂ => (g, h)) :=
    continuous_const.prodMk continuous_id
  have hA := (continuous_godementSectionIntegrand (m := m) d Φ.continuous hf.1.continuous).comp hpair
  change Continuous A at hA
  have hD : Continuous D :=
    ((Units.continuous_val.comp determinantContinuous.continuous).norm.pow 2)
  have hpos (h : Langlands.GeneralLinear m ℂ) : 0 < D h :=
    pow_pos (norm_pos_iff.mpr (determinant h).ne_zero) _
  have hI (r : ℝ) (hr : b < r) :
      Integrable (fun h => A h * (D h : ℂ) ^ (r : ℂ)) (complexGeneralLinearHaar m) := by
    have hs : (m : ℝ) + M ≤ ((shiftedCharacter d (r : ℂ)).exponent + ((m : ℂ) + 1) / 2).re := by
      rw [shiftedCharacter_exponent, Complex.add_re, Complex.add_re, Complex.ofReal_re]
      dsimp only [b, B] at hr
      linarith
    have hc := hM (shiftedCharacter d (r : ℂ)) Φ f hf hs g
    have heq : godementSectionIntegrand (shiftedCharacter d (r : ℂ)) Φ f g =
        fun h => A h * (D h : ℂ) ^ (r : ℂ) :=
      funext fun h => godementSectionIntegrand_shifted d (r : ℂ) Φ f g h
    rwa [heq] at hc
  have hMellin := differentiableOn_mellin_right hA.aestronglyMeasurable hD.measurable.aemeasurable
    hpos hI
  have hE : Differentiable ℂ (fun s : ℂ =>
      Complex.exp (s * (Real.log (complexNormalizedAbs (determinant g : ℂ)) : ℂ))) :=
    (differentiable_id.mul_const _).cexp
  have hC : Differentiable ℂ (fun _ : ℂ =>
      characterWeight d ((m : ℂ) / 2) (determinant g)) := differentiable_const _
  have hprod := (hC.mul hE).differentiableOn.mul hMellin
  have hset : {s : ℂ | B < d.exponent.re + s.re} = {s : ℂ | b < s.re} := by
    ext s
    change B < d.exponent.re + s.re ↔ B - d.exponent.re < s.re
    constructor <;> intro hs <;> linarith
  rw [hset]
  apply hprod.congr
  intro s _
  change godementSectionShift (complexGeneralLinearHaar m) d Φ f g s =
    (characterWeight d ((m : ℂ) / 2) (determinant g) *
      Complex.exp (s * (Real.log (complexNormalizedAbs (determinant g : ℂ)) : ℂ))) *
      ∫ h, A h * (D h : ℂ) ^ s ∂complexGeneralLinearHaar m
  have hpow (h : Langlands.GeneralLinear m ℂ) :
      (D h : ℂ) ^ s = Complex.exp (s * (Real.log (D h) : ℂ)) :=
    normPower_eq_exp (determinant h) s
  simp only [hpow]
  rfl

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
