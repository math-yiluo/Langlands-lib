import Langlands.Global.RankinSelberg.AdelicSimpleRootGauge

/-! # Rectangular Mellin convergence for adelic simple-root gauges -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance rectangularGaugeStatementSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

local instance rectangularGaugeStatementRectangleMeasurableSpace
    (F : Type u) [Field F] [NumberField F] (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _

/-- A common right half-plane of absolute convergence for all adelic simple-root
gauges of a fixed exponent restricted to the rectangular chart. -/
def AdelicSimpleRootGaugeRectangularMellinStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (h : t < r) (τ : ℝ), 0 ≤ τ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ Ξ : Points F (r + 1) → ℝ≥0∞,
        IsAdelicSimpleRootGauge F r τ Ξ → ∀ σ : ℝ, C < σ →
          ∫⁻ p : WhittakerQuotient F (t + 1),
              (∫⁻ x, Ξ (rectangularPoint F h p.out x)
                ∂rectangleMeasure F (r - (t + 1)) (t + 1)) *
                ENNReal.ofReal (detNorm F (t + 1) p.out ^ σ)
            ∂whittakerQuotientMeasure F (t + 1) < ⊤

end Langlands.Global.RankinSelbergGlobal
