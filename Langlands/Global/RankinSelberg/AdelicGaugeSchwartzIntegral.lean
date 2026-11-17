import Langlands.Global.RankinSelberg.AdelicGaugeCompactTranslate
import Langlands.Global.RankinSelberg.WhittakerCompactTorusIntegral

/-! # From a diagonal Mellin bound to a gauge--Schwartz quotient integral -/

noncomputable section
universe u
open NumberField MeasureTheory Set
open scoped Classical CategoryTheory.MonObj NNReal ENNReal
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Global Unfolding AdelicDiagonalUnipotentModulus

local instance gaugeIntegralSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _

variable (F : Type u) [Field F] [NumberField F]

/-- The nonnegative kernel on the actual adelic group whose descent is
integrated against the Whittaker quotient measure. -/
def gaugeSchwartzKernel (r : ℕ) (Ξ : Points F (r + 1) → ℝ≥0∞)
    (Φ : RowVector F (r + 1) → ℂ) (σ : ℝ) (g : Points F (r + 1)) : ℝ≥0∞ :=
  Ξ g * ‖Φ (lastRow F r g)‖ₑ *
    ENNReal.ofReal (detNorm F (r + 1) g ^ σ)

theorem measurable_gaugeSchwartzKernel [CompactSpace (AdeleQuotient F)]
    (r : ℕ) {τ : ℝ} {Ξ : Points F (r + 1) → ℝ≥0∞}
    (hΞ : IsAdelicSimpleRootGauge F r τ Ξ)
    {Φ : RowVector F (r + 1) → ℂ} (hΦ : Φ ∈ schwartzBruhat F (r + 1))
    (σ : ℝ) : Measurable (gaugeSchwartzKernel F r Ξ Φ σ) := by
  have hrow := ((EqualAnalytic.schwartzBruhat_properties F (r + 1) hΦ).1.comp
    (EqualUnfolding.continuous_lastRow F r)).measurable.enorm
  have hdet : Measurable fun g : Points F (r + 1) =>
      ENNReal.ofReal (detNorm F (r + 1) g ^ σ) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_detNorm F (r + 1)).rpow_const fun g =>
        Or.inl (detNorm_pos F (r + 1) g).ne').measurable
  exact (hΞ.2.1.mul hrow).mul hdet

theorem gaugeSchwartzKernel_unipotent_mul (r : ℕ)
    {τ : ℝ} {Ξ : Points F (r + 1) → ℝ≥0∞}
    (hΞ : IsAdelicSimpleRootGauge F r τ Ξ)
    (Φ : RowVector F (r + 1) → ℂ) (σ : ℝ)
    (v : unipotentAdelic F (r + 1)) (g : Points F (r + 1)) :
    gaugeSchwartzKernel F r Ξ Φ σ ((v : Points F (r + 1)) * g) =
      gaugeSchwartzKernel F r Ξ Φ σ g := by
  simp only [gaugeSchwartzKernel, hΞ.2.2.1, EqualUnfolding.lastRow_unipotent_mul,
    detNorm_mul, detNorm_unipotent, one_mul]

local instance gaugeIntegralIdeleMeasurable : MeasurableSpace (Ideles F) := borel _
local instance gaugeIntegralIdeleBorel : BorelSpace (Ideles F) := ⟨rfl⟩

/-- The diagonal majorant, including the inverse positive-root modulus. -/
def gaugeSchwartzTorusMajorant (r : ℕ) (τ σ : ℝ)
    (φ : RowVector F r → ℂ) (ψ : RowVector F 1 → ℂ)
    (d : Fin (r + 1) → Ideles F) : ℝ≥0∞ :=
  (((diagonalModulus F (r + 1) d : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) *
    ENNReal.ofReal (gaugeSimpleRootNormProduct F r d ^ (-τ)) *
    ‖φ (gaugeSimpleRootRow F r d)‖ₑ *
    ‖ψ (singleRow F (d (Fin.last r) : Adeles F))‖ₑ *
    ENNReal.ofReal (detNorm F (r + 1) (gaugeDiagonalPoint F (r + 1) d) ^ σ)

/-- Finiteness of the separated diagonal majorants implies finiteness on
the actual Whittaker quotient. -/
theorem lintegral_gaugeSchwartzKernel_lt_top_of_torusMajorant
    [CompactSpace (AdeleQuotient F)] (r : ℕ)
    {τ : ℝ} {Ξ : Points F (r + 1) → ℝ≥0∞}
    (hΞ : IsAdelicSimpleRootGauge F r τ Ξ)
    {Φ : RowVector F (r + 1) → ℂ} (hΦ : Φ ∈ schwartzBruhat F (r + 1))
    (σ : ℝ) (mu : Measure (Fin (r + 1) → Ideles F)) [mu.IsHaarMeasure]
    (htorus : ∀ (φ : RowVector F r → ℂ), φ ∈ schwartzBruhat F r →
      ∀ (ψ : RowVector F 1 → ℂ), ψ ∈ schwartzBruhat F 1 →
        ∫⁻ d, gaugeSchwartzTorusMajorant F r τ σ φ ψ d ∂mu < ⊤) :
    ∫⁻ q : WhittakerQuotient F (r + 1),
      gaugeSchwartzKernel F r Ξ Φ σ q.out
        ∂whittakerQuotientMeasure F (r + 1) < ⊤ := by
  apply WhittakerCompactTorusIntegral.lintegral_whittakerQuotient_lt_top_of_compactTorusBound
    F (r + 1) mu (gaugeSchwartzKernel F r Ξ Φ σ)
    (measurable_gaugeSchwartzKernel F r hΞ hΦ σ)
    (gaugeSchwartzKernel_unipotent_mul F r hΞ Φ σ)
  intro C hC
  obtain ⟨φ, hφ, ψ, hψ, A, hA, hbound⟩ :=
    exists_compact_gaugeSchwartz_kernel_majorant F r hΞ hΦ hC σ
  refine ⟨ENNReal.ofReal A *
    ∫⁻ d, gaugeSchwartzTorusMajorant F r τ σ φ ψ d ∂mu,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (htorus φ hφ ψ hψ), ?_⟩
  intro c hc
  calc
    _ ≤ ∫⁻ d, ENNReal.ofReal A *
        gaugeSchwartzTorusMajorant F r τ σ φ ψ d ∂mu := by
      apply lintegral_mono
      intro d
      have h := mul_le_mul_left
        (hbound d c hc)
        (((diagonalModulus F (r + 1) d : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞)
      dsimp only [gaugeSchwartzKernel, gaugeSchwartzTorusMajorant]
      convert h using 1 <;> ac_rfl
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end Langlands.Global.RankinSelbergGlobal
