import Langlands.Global.RankinSelberg.RealGapNormalizedWeighted

/-! # Diagonal Mellin moments on the normalized ordinary real gap chart -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealGapNormalizedWeighted

open Langlands.Archimedean (unitaryCompact)
open Langlands.LocalFactor.Archimedean (RealBlock)
open ArchimedeanLocal (RealQuotientMeasureData realNormalizedAbs)
open RealGapLeadingSchwartz (matrixDecay)
open RealGapTriangularChart (Outer)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℝ
local notation "Size" => fun t q => t + 1 + q + 1
local notation "Rect" => fun t q => Mat (q + 1) (t + 1)
local notation "δ" => fun g => realNormalizedAbs (Matrix.det (Units.val g))
local instance gapPowerMomentGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _

/-- The ordinary split kernel has all sufficiently large diagonal Mellin moments. -/
def RealGapNormalizedPowerMomentStatement : Prop :=
  ∀ (t q : ℕ) (a : ℝˣ) (D : RealQuotientMeasureData t) (η₁ : Measure (G (t + 1)))
    (κ : Measure (unitaryCompact ℝ (Size t q))),
    η₁.IsHaarMeasure → κ.IsHaarMeasure →
    ∀ (ds es : List RealBlock) (W : G (Size t q) → ℂ) (V : G (t + 1) → ℂ),
      W ∈ realUniformWhittakerModel (t + 1 + q) ds (-a) → V ∈ realUniformWhittakerModel t es a →
    ∀ (β : ℝ), ∃ σ₀ : ℝ, ∀ σ : ℝ, σ₀ ≤ σ →
      ∀ (Φ₀ : 𝓢(Mat (Size t q) (t + 1), ℂ)) (Φ Ψ : 𝓢((Fin (Size t q) → ℝ), ℂ))
        (Ξ : Fin q → 𝓢((Fin (Size t q) → ℝ), ℂ)) (w : Outer (t + 1) q → ℂ),
        Measurable w → (∀ p, ‖w p‖ ≤ δ p.1.1.1 ^ β) →
        Integrable (normalizedWeightedKernel false a Φ₀ Φ Ψ Ξ W V 0
          (fun x : ℝ => (x ^ σ : ℝ)) (fun x : ℝ => (x ^ σ : ℝ)) w)
          (normalizedGapMeasure t q a D (Measure.dirac (0 : Rect t q)) η₁ κ)

set_option maxHeartbeats 700000 in
theorem realGapNormalizedPowerMoment : RealGapNormalizedPowerMomentStatement := by
  intro t q a D η₁ κ hη₁ hκ ds es W V hWm hVm β
  let νY := Measure.dirac (0 : Rect t q)
  have hY : Integrable (matrixDecay 0) νY := integrable_dirac (by simp)
  obtain ⟨u, v, hI⟩ := realGapNormalizedPowerBounds t q a D νY η₁ κ hη₁ hκ inferInstance 0 hY ds es W V
    hWm hVm 0 β
  refine ⟨max 0 (max u v), ?_⟩
  intro σ hσ Φ₀ Φ Ψ Ξ w hw hwB
  have h₀ : 0 ≤ σ := (le_max_left _ _).trans hσ
  have hu : u ≤ σ := (le_max_left _ _).trans ((le_max_right _ _).trans hσ)
  have hv : v ≤ σ := (le_max_right _ _).trans ((le_max_right _ _).trans hσ)
  let f := fun x : ℝ => ((x ^ σ : ℝ) : ℂ)
  have hfm : Measurable f := (Complex.continuous_ofReal.comp (Real.continuous_rpow_const h₀)).measurable
  have hf (x : ℝ) (hx : 0 < x) : ‖f x‖ ≤ 1 * x ^ σ := by
    simp [f, abs_of_nonneg (Real.rpow_nonneg hx.le σ)]
  refine hI false Φ₀ Φ Ψ Ξ f f w 1 0 σ σ 1 1 zero_le_one le_rfl hu hv hw hfm hfm hf hf ?_
  simpa [RealGapAlternateWeighted.leadingSide] using hwB

end Langlands.Global.RankinSelbergGlobal.RealGapNormalizedWeighted
