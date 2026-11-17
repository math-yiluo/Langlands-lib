import Langlands.Global.RankinSelberg.WhittakerSchwartzGaugeStatement
import Langlands.Global.RankinSelberg.WhittakerSimpleRootMajorizationStatement
import Langlands.Global.RankinSelberg.AdelicGaugeSchwartzIntegral

/-! # Reduction of the weighted Whittaker–Schwartz estimate to simple-root gauges -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding

local instance schwartzReductionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

local instance schwartzReductionIdeleMeasurable (F : Type u) [Field F] [NumberField F] :
    MeasurableSpace (Ideles F) := borel _
local instance schwartzReductionIdeleBorel (F : Type u) [Field F] [NumberField F] :
    BorelSpace (Ideles F) := ⟨rfl⟩

/-- Pointwise majorization and a uniform bound for the concrete diagonal
majorants imply the unchanged Whittaker–Schwartz statement. -/
theorem whittakerSchwartzGauge_of_majorization_torusMajorants
    (hmajor : WhittakerSimpleRootMajorizationStatement.{u})
    (htorus : ∀ (F : Type u) [Field F] [NumberField F]
      [CompactSpace (AdeleQuotient F)] (r : ℕ) (τ : ℝ), 0 ≤ τ →
      ∃ C : ℝ, 0 ≤ C ∧
        ∃ mu : Measure (Fin (r + 1) → Ideles F), mu.IsHaarMeasure ∧
          ∀ σ : ℝ, C < σ →
            ∀ (φ : RowVector F r → ℂ), φ ∈ schwartzBruhat F r →
              ∀ (θ : RowVector F 1 → ℂ), θ ∈ schwartzBruhat F 1 →
                ∫⁻ d, gaugeSchwartzTorusMajorant F r τ σ φ θ d ∂mu < ⊤) :
    WhittakerSchwartzGaugeStatement.{u} := by
  intro F _ _ _ r V R hV hcentral
  obtain ⟨β, hβ⟩ := hcentral
  obtain ⟨τ, hτ, hτmajor⟩ := hmajor F r V R hV β hβ
  obtain ⟨C, _, mu, hmu, hCtorus⟩ := htorus F r τ hτ
  let : mu.IsHaarMeasure := hmu
  refine ⟨max 0 (C - β), le_max_left _ _, ?_⟩
  intro ψ hψ f Φ hΦ σ hσ
  obtain ⟨Ξ, hΞ, hΞmajor⟩ := hτmajor ψ hψ f
  have hshift : C < σ + β := by
    have := lt_of_le_of_lt (le_max_right 0 (C - β)) hσ
    linarith
  have hfinite := lintegral_gaugeSchwartzKernel_lt_top_of_torusMajorant
    F r hΞ hΦ (σ + β) mu (hCtorus (σ + β) hshift)
  change ∫⁻ p : WhittakerQuotient F (r + 1),
      Ξ p.out * ‖Φ (lastRow F r p.out)‖ₑ *
        ENNReal.ofReal (detNorm F (r + 1) p.out ^ (σ + β))
      ∂whittakerQuotientMeasure F (r + 1) < ⊤ at hfinite
  refine lt_of_le_of_lt (lintegral_mono fun p => ?_) hfinite
  calc
    ‖whittaker F r ψ f p.out‖ₑ * ‖Φ (lastRow F r p.out)‖ₑ *
        ENNReal.ofReal (detNorm F (r + 1) p.out ^ σ) ≤
      (ENNReal.ofReal (detNorm F (r + 1) p.out ^ β) * Ξ p.out) *
        ‖Φ (lastRow F r p.out)‖ₑ *
          ENNReal.ofReal (detNorm F (r + 1) p.out ^ σ) := by
            gcongr
            exact hΞmajor p.out
    _ = Ξ p.out * ‖Φ (lastRow F r p.out)‖ₑ *
        ENNReal.ofReal (detNorm F (r + 1) p.out ^ (σ + β)) := by
      rw [Real.rpow_add (detNorm_pos F (r + 1) p.out),
        ENNReal.ofReal_mul (Real.rpow_nonneg (detNorm_pos F (r + 1) p.out).le σ)]
      ac_rfl

end Langlands.Global.RankinSelbergGlobal
