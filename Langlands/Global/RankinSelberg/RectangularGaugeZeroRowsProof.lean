import Langlands.Global.RankinSelberg.RectangularGaugeEmptyRectangle
import Langlands.Global.RankinSelberg.AdelicSchwartzMellinHaar
import Langlands.Global.RankinSelberg.AdelicSimpleRootGaugeMellinProof
import Langlands.Global.RankinSelberg.RectangularGaugeMellinStatement

/-! # The zero-row branch of rectangular gauge Mellin convergence -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance zeroRowsSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

local instance zeroRowsRectangleMeasurableSpace
    (F : Type u) [Field F] [NumberField F] (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _

/-- In the zero-row case the iterated rectangular integral is exactly the
padded integral, for every kernel and exponent. -/
theorem rectangular_mellin_eq_padded_of_gap_eq_zero
    (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    {r t : ℕ} (h : t < r) (hgap : r - (t + 1) = 0)
    (Ξ : Points F (r + 1) → ℝ≥0∞) (σ : ℝ) :
    (∫⁻ p : WhittakerQuotient F (t + 1),
      (∫⁻ x, Ξ (rectangularPoint F h p.out x)
        ∂rectangleMeasure F (r - (t + 1)) (t + 1)) *
        ENNReal.ofReal (detNorm F (t + 1) p.out ^ σ)
      ∂whittakerQuotientMeasure F (t + 1)) =
    ∫⁻ p : WhittakerQuotient F (t + 1),
      Ξ (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) p.out) *
        ENNReal.ofReal (detNorm F (t + 1) p.out ^ σ)
      ∂whittakerQuotientMeasure F (t + 1) := by
  apply lintegral_congr
  intro p
  rw [lintegral_rectangular_eq_pad_of_gap_eq_zero F h hgap]

/-- The zero-row branch has a common half-plane of convergence for every
simple-root gauge of the supplied exponent. -/
theorem adelicSimpleRootGaugeRectangularMellin_of_gap_eq_zero
    (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (h : t < r) (hgap : r - (t + 1) = 0) (τ : ℝ) (hτ : 0 ≤ τ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Ξ : Points F (r + 1) → ℝ≥0∞,
      IsAdelicSimpleRootGauge F r τ Ξ → ∀ σ : ℝ, C < σ →
        ∫⁻ p : WhittakerQuotient F (t + 1),
          (∫⁻ x, Ξ (rectangularPoint F h p.out x)
            ∂rectangleMeasure F (r - (t + 1)) (t + 1)) *
            ENNReal.ofReal (detNorm F (t + 1) p.out ^ σ)
          ∂whittakerQuotientMeasure F (t + 1) < ⊤ := by
  obtain ⟨C, hC, hfinite⟩ := adelicSimpleRootGaugeMellin F r t h τ hτ
  refine ⟨C, hC, fun Ξ hΞ σ hσ => ?_⟩
  rw [rectangular_mellin_eq_padded_of_gap_eq_zero F h hgap]
  exact hfinite Ξ hΞ σ hσ

end Langlands.Global.RankinSelbergGlobal
