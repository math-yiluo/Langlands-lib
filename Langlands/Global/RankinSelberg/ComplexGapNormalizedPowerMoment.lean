import Langlands.Global.RankinSelberg.ComplexGapNormalizedWeighted

/-! # Diagonal Mellin moments on the normalized ordinary gap chart -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapNormalizedWeighted

open Langlands.Archimedean (unitaryCompact)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ArchimedeanLocal (ComplexQuotientMeasureData complexNormalizedAbs)
open ComplexGapLeadingSchwartz (matrixDecay)
open ComplexGapTriangularChart (Outer)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℂ
local notation "Size" => fun t q => t + 1 + q + 1
local notation "Rect" => fun t q => Mat (q + 1) (t + 1)
local notation "δ" => fun g => complexNormalizedAbs (Matrix.det (Units.val g))
local instance gapPowerMomentGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _

/-- The ordinary split kernel has all sufficiently large diagonal Mellin moments. -/
def ComplexGapNormalizedPowerMomentStatement : Prop :=
  ∀ (t q : ℕ) (a : ℂˣ) (D : ComplexQuotientMeasureData t) (κ : Measure (unitaryCompact ℂ (Size t q))),
    κ.IsHaarMeasure →
    ∀ (ds es : List ComplexCharacterData) (W : complexWhittakerModel (t + 1 + q) ds (-a))
      (V : complexWhittakerModel t es a) (β : ℝ),
    ∃ σ₀ : ℝ, ∀ σ : ℝ, σ₀ ≤ σ →
      ∀ (Φ₀ : 𝓢(Mat (Size t q) (t + 1), ℂ)) (Φ Ψ : 𝓢((Fin (Size t q) → ℂ), ℂ))
        (Ξ : Fin q → 𝓢((Fin (Size t q) → ℂ), ℂ)) (w : Outer (t + 1) q → ℂ),
        Measurable w → (∀ p, ‖w p‖ ≤ δ p.1.1.1 ^ β) →
        Integrable (normalizedWeightedKernel false a Φ₀ Φ Ψ Ξ W.val V.val 0
          (fun x : ℝ => (x ^ σ : ℝ)) (fun x : ℝ => (x ^ σ : ℝ)) w)
          (normalizedGapMeasure t q a D (Measure.dirac (0 : Rect t q)) κ)

set_option maxHeartbeats 700000 in
theorem complexGapNormalizedPowerMoment : ComplexGapNormalizedPowerMomentStatement := by
  intro t q a D κ hκ ds es W V β
  let νY := Measure.dirac (0 : Rect t q)
  have hY : Integrable (matrixDecay 0) νY := integrable_dirac (by simp)
  obtain ⟨u, v, hI⟩ := complexGapNormalizedPowerBounds t q a D νY κ hκ inferInstance 0 hY ds es W V 0 β
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
  simpa [ComplexGapAlternateWeighted.leadingSide] using hwB

end Langlands.Global.RankinSelbergGlobal.ComplexGapNormalizedWeighted
