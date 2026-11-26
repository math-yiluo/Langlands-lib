import Langlands.Global.RankinSelberg.RealGodementPaddedRestriction
import Langlands.Global.RankinSelberg.RealTwoBlockEntries

/-! # Two-block restriction of the real Godement coefficient -/

noncomputable section

open MeasureTheory
open Langlands.LocalFactor.Archimedean Langlands.HarmonicAnalysis
open Langlands.RankinSelberg (lastRow rectangularMeasure)
open scoped NNReal ENNReal SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodementTwoBlockRestriction

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (determinant)
open ArchimedeanLocal RealGodement RealJacquet
open RealGodementPaddedRestriction (paddedRestrictionKernel realGodementPaddedRestriction)
open RealTwoBlockHaar

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "K" => fun n => unitaryCompact ℝ n
local notation "YSpace" => fun n k => Matrix (Fin k) (Fin (n - k)) ℝ
local notation "Coords" => fun n k => ((G k × G (n - k)) × YSpace n k) × K n
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs

local instance twoBlockRestrictionGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance twoBlockRestrictionGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance twoBlockRestrictionNMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := borel _
local instance twoBlockRestrictionNBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
local instance twoBlockRestrictionQMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.RankinSelberg.LeftUnipotentQuotient n ℝ) := borel _

/-- The product measure with the lower-right determinant density of the right-tail chart. -/
def rightTailProductMeasure (n k : ℕ) (ν : AdditiveHaarMeasure ℝ) (μ₁ : Measure (G k))
    (μ₂ : Measure (G (n - k))) (κ : Measure (K n)) : Measure (Coords n k) :=
  (((μ₁.prod μ₂).prod (rectangularMeasure ν k (n - k))).prod κ).withDensity
    (fun p => (rightTailWeight (k := k) p.1.1.2 : ℝ≥0∞))

/-- The two-block integrand on the right-tail coordinates. The row frequency comes from the
right tail, and the two determinant weights are separated. -/
def twoBlockRestrictionKernel {r k : ℕ} (hk : 0 < k) (hkn : k < r + 1) (c : RealCharacterData)
    (a : ℝˣ) (F : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ → ℂ) (f : (Fin (r + 1) → ℝ) → ℂ)
    (U : G (r + 1) → ℂ) (g : G k) (b : G (r + 1)) (p : Coords (r + 1) k) : ℂ :=
  let h₁ := p.1.1.1
  let h₂ := rightTail hk hkn p.1.1.2 p.1.2 p.2
  F (h₂ * diagonalBlocks hk hkn h₁ 1 * b).val * realFourierTransform a f (lastRow h₂⁻¹) *
    U (padGL hkn.le (g * h₁⁻¹) * h₂⁻¹) *
    (detCharacter c.character.toMonoidHom h₁ * P h₁ ((r : ℂ) / 2)) *
    (detCharacter c.character.toMonoidHom h₂ * P h₂ ((r : ℂ) / 2))

/-- The two-block kernel is the pullback of the padded kernel along the right Haar chart. -/
theorem twoBlockRestrictionKernel_chart {r k : ℕ} (hk : 0 < k) (hkn : k < r + 1)
    (c : RealCharacterData) (a : ℝˣ) (F : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ → ℂ)
    (f : (Fin (r + 1) → ℝ) → ℂ) (U : G (r + 1) → ℂ) (g : G k) (b : G (r + 1))
    (p : Coords (r + 1) k) :
    paddedRestrictionKernel c a F f U (padGL hkn.le g) b
        (rightTail hk hkn p.1.1.2 p.1.2 p.2 * diagonalBlocks hk hkn p.1.1.1 1) =
      twoBlockRestrictionKernel hk hkn c a F f U g b p := by
  let η : ℝˣ →* ℂˣ := c.character.toMonoidHom
  let h₁ := p.1.1.1
  let h₂ := rightTail hk hkn p.1.1.2 p.1.2 p.2
  let A := diagonalBlocks hk hkn h₁ 1
  have hs : padGL hkn.le g * (h₂ * A)⁻¹ = padGL hkn.le (g * h₁⁻¹) * h₂⁻¹ := by
    dsimp only [A]
    rw [mul_inv_rev, diagonalBlocks_eq_padGL, ← map_inv, ← mul_assoc, ← map_mul]
  have hrow : lastRow (padGL hkn.le (g * h₁⁻¹) * h₂⁻¹) = lastRow h₂⁻¹ := by
    rw [← diagonalBlocks_eq_padGL hk hkn]
    exact lastRow_diagonalBlocks_mul hk hkn _ _
  have hdet : detCharacter η (h₂ * A) * P (h₂ * A) ((r : ℂ) / 2) =
      (detCharacter η h₁ * P h₁ ((r : ℂ) / 2)) * (detCharacter η h₂ * P h₂ ((r : ℂ) / 2)) := by
    have hA : determinant A = determinant h₁ := by
      dsimp only [A]
      rw [determinant_diagonalBlocks, map_one, mul_one]
    have hc : detCharacter η A = detCharacter η h₁ := by
      unfold detCharacter
      rw [hA]
    have hp : P A ((r : ℂ) / 2) = P h₁ ((r : ℂ) / 2) := by
      have hA' : A.val.det = h₁.val.det := congrArg Units.val hA
      unfold ArchimedeanLocal.detPower
      rw [hA']
    rw [detCharacter_mul, realDetPower_mul, hc, hp]
    ring
  unfold paddedRestrictionKernel twoBlockRestrictionKernel
  change F (h₂ * A * b).val * realFourierTransform a f (lastRow (padGL hkn.le g * (h₂ * A)⁻¹)) *
      U (padGL hkn.le g * (h₂ * A)⁻¹) * detCharacter η (h₂ * A) * P (h₂ * A) ((r : ℂ) / 2) = _
  rw [hs, hrow]
  calc
    _ = F (h₂ * A * b).val * realFourierTransform a f (lastRow h₂⁻¹) *
          U (padGL hkn.le (g * h₁⁻¹) * h₂⁻¹) *
          (detCharacter η (h₂ * A) * P (h₂ * A) ((r : ℂ) / 2)) := by ring
    _ = _ := by rw [hdet]; dsimp only; ring

/-- In the right-tail Haar chart the padded Godement value is an absolutely integrable
four-factor integral, with one positive chart constant for each quotient measure datum. -/
def RealGodementTwoBlockRestrictionStatement : Prop :=
  ∀ (r k : ℕ) (hk : 0 < k) (hkn : k < r + 1) (ν : AdditiveHaarMeasure ℝ)
    (μ₁ : Measure (G k)) (μ₂ : Measure (G (r + 1 - k))) (κ : Measure (K (r + 1))),
    μ₁.IsHaarMeasure → μ₂.IsHaarMeasure → κ.IsHaarMeasure → κ.IsInvInvariant →
  ∀ D : RealQuotientMeasureData r, ∃ C : ℝ≥0, 0 < C ∧
    ∀ (ds : List RealBlock) (a : ℝˣ) (c : RealCharacterData)
      (Φ : 𝓢(Matrix (Fin (r + 1)) (Fin (r + 2)) ℝ, ℂ))
      (F : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ → ℂ) (f : (Fin (r + 1) → ℝ) → ℂ),
      (∀ A x, Φ (joinLastColumn A x) = F A * f x) →
    ∀ (U : G (r + 1) → ℂ), U ∈ realUniformWhittakerModel r ds (-a) → ∀ (g : G k) (b : G (r + 1)),
      Integrable (twoBlockRestrictionKernel hk hkn c a F f U g b)
        (rightTailProductMeasure (r + 1) k ν μ₁ μ₂ κ) ∧
      realAdjacentGodementCoefficient D a Φ U c
          (padGL (Nat.succ_le_succ (Nat.le_succ r)) (padGL hkn.le g * b)) =
        realAdjacentWeylSign r c * detCharacter c.character.toMonoidHom b *
          P b (((r + 1 : ℕ) : ℂ) / 2) * P g (1 / 2) * (C : ℂ) *
          ∫ p, twoBlockRestrictionKernel hk hkn c a F f U g b p
            ∂rightTailProductMeasure (r + 1) k ν μ₁ μ₂ κ

set_option maxHeartbeats 800000 in
theorem realGodementTwoBlockRestriction : RealGodementTwoBlockRestrictionStatement := by
  intro r k hk hkn ν μ₁ μ₂ κ hμ₁ hμ₂ hκ hκinv D
  let Haar := D.groupHaar
  let : Haar.IsHaarMeasure := D.groupHaar_isHaar
  let ρ := rightTailProductMeasure (r + 1) k ν μ₁ μ₂ κ
  let chart := fun p : Coords (r + 1) k =>
    rightTail hk hkn p.1.1.2 p.1.2 p.2 * diagonalBlocks hk hkn p.1.1.1 1
  have hChart : Measurable chart := measurable_rightChart hk hkn
  obtain ⟨C, hC, hHaar⟩ := realTwoBlockRightHaar (r + 1) k hk hkn ν Haar μ₁ μ₂ κ
    inferInstance hμ₁ hμ₂ hκ hκinv
  change Haar = C • ρ.map chart at hHaar
  refine ⟨C, hC, ?_⟩
  intro ds a c Φ F f hΦ U hU g b
  let Fk := paddedRestrictionKernel c a F f U (padGL hkn.le g) b
  let F' := twoBlockRestrictionKernel hk hkn c a F f U g b
  have hF' : Fk ∘ chart = F' := funext (twoBlockRestrictionKernel_chart hk hkn c a F f U g b)
  obtain ⟨hF, hValue⟩ := realGodementPaddedRestriction r ds a D c Φ F f hΦ U hU (padGL hkn.le g) b
  change Integrable Fk Haar at hF
  have hMap : Integrable Fk (ρ.map chart) := by
    rw [hHaar] at hF
    exact (integrable_smul_measure (by exact_mod_cast hC.ne') ENNReal.coe_ne_top).mp hF
  have hInt : (∫ h, Fk h ∂Haar) = (C : ℂ) * ∫ p, F' p ∂ρ := by
    rw [hHaar]
    change (∫ h, Fk h ∂(C : ℝ≥0∞) • ρ.map chart) = _
    rw [integral_smul_measure, integral_map hChart.aemeasurable hMap.aestronglyMeasurable,
      ENNReal.coe_toReal, Complex.real_smul, ← hF']
    rfl
  refine ⟨?_, ?_⟩
  · change Integrable F' ρ
    rw [← hF']
    exact (integrable_map_measure hMap.aestronglyMeasurable hChart.aemeasurable).mp hMap
  · rw [hValue]
    change _ * _ * _ * _ * (∫ h, Fk h ∂Haar) = _
    rw [hInt, show P (padGL hkn.le g) (1 / 2) = P g (1 / 2) by
      unfold ArchimedeanLocal.detPower
      rw [UnequalAnalytic.det_padGL]]
    ring

end Langlands.Global.RankinSelbergGlobal.RealGodementTwoBlockRestriction
