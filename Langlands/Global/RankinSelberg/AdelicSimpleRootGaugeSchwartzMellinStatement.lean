import Langlands.Global.RankinSelberg.AdelicSimpleRootGauge
import Langlands.Global.RankinSelberg.EqualIntegrals

/-! # Full-rank Mellin integrability of simple-root gauges with a Schwartz factor -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance schwartzMellinSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

/-- One right half-plane works for every gauge of the specified simple-root
exponent and every Schwartz–Bruhat function of the last row on the full group. -/
def AdelicSimpleRootGaugeSchwartzMellinStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ Ξ : Points F (r + 1) → ℝ≥0∞,
        IsAdelicSimpleRootGauge F r τ Ξ →
          ∀ (Φ : RowVector F (r + 1) → ℂ), Φ ∈ schwartzBruhat F (r + 1) →
            ∀ σ : ℝ, C < σ →
              ∫⁻ p : WhittakerQuotient F (r + 1),
                  Ξ p.out * ‖Φ (lastRow F r p.out)‖ₑ *
                    ENNReal.ofReal (detNorm F (r + 1) p.out ^ σ)
                ∂whittakerQuotientMeasure F (r + 1) < ⊤

end Langlands.Global.RankinSelbergGlobal
