import Langlands.Global.RankinSelberg.RectangularGaugeMellinStatement
import Langlands.Global.RankinSelberg.RectangularGaugeTransfer

/-! # The rectangular Whittaker bound from two analytic gauge inputs -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding

local instance rectangularGaugeReductionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

/-- The nonnegative Whittaker threshold obtained by absorbing a determinant
exponent into a gauge Mellin threshold. -/
def rectangularGaugeThreshold (C β : ℝ) : ℝ := max 0 (C - β)

theorem rectangularGaugeThreshold_nonneg (C β : ℝ) :
    0 ≤ rectangularGaugeThreshold C β :=
  le_max_left _ _

theorem lt_add_of_rectangularGaugeThreshold_lt {C β σ : ℝ}
    (hσ : rectangularGaugeThreshold C β < σ) : C < σ + β := by
  have h := le_max_right 0 (C - β)
  change max 0 (C - β) < σ at hσ
  linarith

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- Uniform pointwise majorization of the translated dual Whittaker functions
and rectangular Mellin convergence imply the published rectangular gauge bound. -/
theorem rectWhittakerGaugeBound_of_simpleRootGauge {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r) (β τ : ℝ) (hτ : 0 ≤ τ)
    (hmajorant : ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
      ∀ v : T.Space, ∃ Ξ : Points F (r + 1) → ℝ≥0∞,
        IsAdelicSimpleRootGauge F r τ Ξ ∧
          ∀ g : Points F (r + 1),
            ‖translateFunction F (r + 1) (unfoldingWeyl F h)
                (dualFunction F (r + 1) (cuspWhittaker F T ψ v)) g‖ₑ ≤
              ENNReal.ofReal (detNorm F (r + 1) g ^ β) * Ξ g)
    (hMellin : AdelicSimpleRootGaugeRectangularMellinStatement.{u}) :
    RectWhittakerGaugeBound F h T := by
  obtain ⟨C, -, hC⟩ := hMellin F r t h τ hτ
  refine ⟨rectangularGaugeThreshold C β, rectangularGaugeThreshold_nonneg C β, ?_⟩
  intro ψ hψ v σ hσ
  obtain ⟨Ξ, hΞ, hW⟩ := hmajorant ψ hψ v
  exact rectangular_mellin_lt_top_of_majorant F h _ Ξ β σ hW
    (hC Ξ hΞ (σ + β) (lt_add_of_rectangularGaugeThreshold_lt hσ))

end Langlands.Global.RankinSelbergGlobal
