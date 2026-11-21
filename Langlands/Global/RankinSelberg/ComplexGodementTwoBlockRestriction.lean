import Langlands.Global.RankinSelberg.ComplexGodementPaddedRestriction
import Langlands.Global.RankinSelberg.ComplexTwoBlockEntries

/-! # Two-block restriction of the complex Godement integral -/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementTwoBlockRestriction

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.GeneralLinear (determinant)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure rectangularJoin)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.RankinSelberg (rectangularMeasure)
open ArchimedeanLocal (complexNormalizedAbs)
open ComplexGodement (characterWeight)
open ComplexGodementAddedCharacter (continuedValue)
open ComplexGodementPaddedRestriction (paddedRestrictionKernel complexGodementPaddedRestriction)
open ComplexGodementPartialFourier (partialSchwartz)
open ComplexTwoBlockHaar

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "K" => fun n => unitaryCompact ℂ n
local notation "Rect" => fun r => Matrix (Fin (r + 1)) (Fin (r + 2)) ℂ
local notation "YSpace" => fun n k => Matrix (Fin k) (Fin (n - k)) ℂ
local notation "Coords" => fun n k => ((G k × G (n - k)) × YSpace n k) × K n
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs

local instance twoBlockRestrictionGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance twoBlockRestrictionGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩

/-- The product measure with the lower-right determinant density of the right-tail chart. -/
def rightTailProductMeasure (n k : ℕ) (ν : AdditiveHaarMeasure ℂ) (κ : Measure (K n)) :
    Measure (Coords n k) :=
  ((((complexGeneralLinearHaar k).prod (complexGeneralLinearHaar (n - k))).prod
    (rectangularMeasure ν k (n - k))).prod κ).withDensity
      (fun p => (rightTailWeight (k := k) p.1.1.2 : ℝ≥0∞))

/-- The two-block integrand on the right-tail coordinates. The inverse-transpose frequency
comes from the right tail. The two determinant characters are separated. -/
def twoBlockRestrictionKernel {r k : ℕ} (hk : 0 < k) (hkn : k < r + 1)
    (μ : AdditiveHaarMeasure ℂ) (d : ComplexCharacterData) (a : ℂˣ)
    (Φ : 𝓢(Rect r, ℂ)) (W : G (r + 1) → ℂ) (g : G k) (b : G (r + 1)) (s : ℂ)
    (p : Coords (r + 1) k) : ℂ :=
  let h₁ := p.1.1.1
  let h₂ := rightTail hk hkn p.1.1.2 p.1.2 p.2
  let e : ℂ := ((r + 2 : ℕ) : ℂ) / 2 + s - 1
  partialSchwartz a μ Φ (rectangularJoin (h₂.val * (diagonalBlocks hk hkn h₁ 1).val * b.val)
    (h₂⁻¹.val (Fin.last r))) * W (padGL hkn.le (g * h₁⁻¹) * h₂⁻¹) *
    characterWeight d e (determinant h₁) * characterWeight d e (determinant h₂)

private theorem twoBlockRestrictionKernel_chart {r k : ℕ} (hk : 0 < k) (hkn : k < r + 1)
    (μ : AdditiveHaarMeasure ℂ) (d : ComplexCharacterData) (a : ℂˣ)
    (Φ : 𝓢(Rect r, ℂ)) (W : G (r + 1) → ℂ) (g : G k) (b : G (r + 1)) (s : ℂ)
    (p : Coords (r + 1) k) :
    paddedRestrictionKernel μ d a Φ W (padGL hkn.le g) b s
        (rightTail hk hkn p.1.1.2 p.1.2 p.2 * diagonalBlocks hk hkn p.1.1.1 1) =
      twoBlockRestrictionKernel hk hkn μ d a Φ W g b s p := by
  let h₁ := p.1.1.1
  let h₂ := rightTail hk hkn p.1.1.2 p.1.2 p.2
  let A := diagonalBlocks hk hkn h₁ 1
  have hs : padGL hkn.le g * (h₂ * A)⁻¹ = padGL hkn.le (g * h₁⁻¹) * h₂⁻¹ := by
    dsimp only [A]
    rw [mul_inv_rev, diagonalBlocks_eq_padGL, ← map_inv, ← mul_assoc, ← map_mul]
  have hrow : (padGL hkn.le (g * h₁⁻¹) * h₂⁻¹).val (Fin.last r) = h₂⁻¹.val (Fin.last r) := by
    rw [← diagonalBlocks_eq_padGL hk hkn]
    exact lastRow_diagonalBlocks_mul hk hkn _ _
  have hdet : determinant (h₂ * A) = determinant h₁ * determinant h₂ := by
    dsimp only [A]
    rw [map_mul, determinant_diagonalBlocks, map_one, mul_one, mul_comm]
  let χ := characterWeight d (((r + 2 : ℕ) : ℂ) / 2 + s - 1)
  have hχ : χ (determinant (h₂ * A)) = χ (determinant h₁) * χ (determinant h₂) := by
    rw [hdet, map_mul]
  unfold paddedRestrictionKernel twoBlockRestrictionKernel
  change partialSchwartz a μ Φ (rectangularJoin ((h₂ * A).val * b.val)
      ((padGL hkn.le g * (h₂ * A)⁻¹).val (Fin.last r))) * W (padGL hkn.le g * (h₂ * A)⁻¹) *
        χ (determinant (h₂ * A)) = _
  rw [hs, hrow, hχ, Units.val_mul]
  simp only [mul_assoc]
  rfl

/-- In the right-tail Haar chart the padded Godement value is an absolutely integrable
four-factor integral, with a single positive chart constant independent of the tests and
exponents. The factor `b` permits a lower rectangle in the argument of the larger value. -/
def ComplexGodementTwoBlockRestrictionStatement : Prop :=
  ∀ (r k : ℕ) (hk : 0 < k) (hkn : k < r + 1) (ν : AdditiveHaarMeasure ℂ)
    (κ : Measure (K (r + 1))), κ.IsHaarMeasure → κ.IsInvInvariant →
  ∃ c : ℝ≥0, 0 < c ∧
    ∀ (ds : List ComplexCharacterData) (a : ℂˣ) (μ : AdditiveHaarMeasure ℂ)
      (d : ComplexCharacterData) (Φ : 𝓢(Rect r, ℂ)) (W : complexWhittakerModel r ds (-a))
      (g : G k) (b : G (r + 1)) (s : ℂ),
      Integrable (twoBlockRestrictionKernel hk hkn μ d a Φ W.val g b s)
        (rightTailProductMeasure (r + 1) k ν κ) ∧
      continuedValue (complexGeneralLinearHaar (r + 1)) μ d a Φ W.val
          (padGL (Nat.le_succ (r + 1)) (padGL hkn.le g * b)) s =
        (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) * P g (1 / 2) *
          characterWeight d (((r + 1 : ℕ) : ℂ) / 2 + s) (determinant b) *
          (c : ℂ) * ∫ p, twoBlockRestrictionKernel hk hkn μ d a Φ W.val g b s p
            ∂rightTailProductMeasure (r + 1) k ν κ

set_option maxHeartbeats 800000 in
theorem complexGodementTwoBlockRestriction : ComplexGodementTwoBlockRestrictionStatement := by
  intro r k hk hkn ν κ hκ hκinv
  let Haar := complexGeneralLinearHaar (r + 1)
  let ρ := rightTailProductMeasure (r + 1) k ν κ
  let chart := fun p : Coords (r + 1) k =>
    rightTail hk hkn p.1.1.2 p.1.2 p.2 * diagonalBlocks hk hkn p.1.1.1 1
  have hChart : Measurable chart := measurable_rightChart hk hkn
  obtain ⟨c, hc, hHaar⟩ := complexTwoBlockRightHaar (r + 1) k hk hkn ν κ hκ hκinv
  change Haar = c • ρ.map chart at hHaar
  refine ⟨c, hc, ?_⟩
  intro ds a μ d Φ W g b s
  let F := paddedRestrictionKernel μ d a Φ W.val (padGL hkn.le g) b s
  let F' := twoBlockRestrictionKernel hk hkn μ d a Φ W.val g b s
  have hF' : F ∘ chart = F' := funext (twoBlockRestrictionKernel_chart hk hkn μ d a Φ W.val g b s)
  obtain ⟨hF, hValue⟩ := complexGodementPaddedRestriction r ds a Haar
    (by infer_instance) (by infer_instance) μ d Φ W (padGL hkn.le g) b s
  change Integrable F Haar at hF
  have hMap : Integrable F (ρ.map chart) := by
    rw [hHaar] at hF
    exact (integrable_smul_measure (by exact_mod_cast hc.ne') ENNReal.coe_ne_top).mp hF
  have hInt : (∫ h, F h ∂Haar) = (c : ℂ) * ∫ p, F' p ∂ρ := by
    rw [hHaar]
    change (∫ h, F h ∂(c : ℝ≥0∞) • ρ.map chart) = _
    rw [integral_smul_measure, integral_map hChart.aemeasurable hMap.aestronglyMeasurable,
      ENNReal.coe_toReal, Complex.real_smul, ← hF']
    rfl
  refine ⟨?_, ?_⟩
  · change Integrable F' ρ
    rw [← hF']
    exact (integrable_map_measure hMap.aestronglyMeasurable hChart.aemeasurable).mp hMap
  · rw [hValue]
    change _ * _ * _ * (∫ h, F h ∂Haar) = _
    rw [hInt, show P (padGL hkn.le g) (1 / 2) = P g (1 / 2) by
      unfold ArchimedeanLocal.detPower
      rw [UnequalAnalytic.det_padGL]]
    simp only [mul_assoc]
    rfl

end Langlands.Global.RankinSelbergGlobal.ComplexGodementTwoBlockRestriction
