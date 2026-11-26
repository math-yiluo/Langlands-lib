import Langlands.Global.RankinSelberg.RealGapDualHaar

/-! # Common product-determinant moments on the full real dual chart -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapDualPowerMoment

open Langlands.Archimedean (unitaryCompact)
open Langlands.LocalFactor.Archimedean (RealBlock RealCharacterData)
open Langlands.RankinSelberg (rectangularMeasure)
open ArchimedeanLocal (RealQuotientMeasureData realSelfDualMeasure)
open RealGapAlternateRestriction (GodementColumnFactors)
open RealGapDualHaar (dualChartMeasure dualChartWeightedKernel realGapDualHaarPowerBounds)

local instance gapDualMomentGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) :=
  borel _
local instance gapDualMomentGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
local instance gapDualMomentUMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := borel _
local instance gapDualMomentUBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
local instance gapDualMomentQMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.RankinSelberg.LeftUnipotentQuotient n ℝ) := borel _
local instance gapDualMomentQBorel (n : ℕ) :
    BorelSpace (Langlands.RankinSelberg.LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

variable (t q : ℕ)
local notation "k" => t + 1
local notation "r" => t + 1 + q
local notation "n" => t + 1 + q + 1
local notation "Sq" => Matrix (Fin n) (Fin n) ℝ

/-- The unintegrated dual chart admits the same complex Mellin power in both determinant
variables, on a sufficiently far right half-plane. -/
def RealGapDualPowerMomentStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (a : ℝˣ) (η₁ : Measure (Langlands.GeneralLinear k ℝ))
    (κ : Measure (unitaryCompact ℝ n)), η₁.IsHaarMeasure → κ.IsHaarMeasure → κ.IsInvInvariant →
    ∀ (ds es : List RealBlock) (Wd : Langlands.GeneralLinear n ℝ → ℂ)
      (Vd : Langlands.GeneralLinear k ℝ → ℂ),
      Wd ∈ realUniformWhittakerModel r ds a → Vd ∈ realUniformWhittakerModel t es (-a) →
    ∀ (c : RealCharacterData) (Fs : 𝓢(Sq, ℂ)) (T : GodementColumnFactors k q),
      (∀ B, Fs B = T.squareEval k q B) →
    ∃ σ : ℝ, ∀ s : ℂ, σ ≤ s.re →
      Integrable (dualChartWeightedKernel t q a c Fs T Wd Vd
        (fun x : ℝ => (x : ℂ) ^ s) (fun x : ℝ => (x : ℂ) ^ s))
        (D.measure.prod ((rectangularMeasure (realSelfDualMeasure a) (n - k) k).prod
          (dualChartMeasure t q a η₁ κ)))

theorem realGapDualPowerMoment : RealGapDualPowerMomentStatement t q := by
  intro D a η₁ κ hη₁ hκ hκinv ds es Wd Vd hWd hVd c Fs T hT
  obtain ⟨α, γ, hI⟩ := realGapDualHaarPowerBounds t q D a η₁ κ hκinv ds es Wd Vd hWd hVd c Fs T hT
  refine ⟨max α γ, ?_⟩
  intro s hs
  let f (x : ℝ) := (x : ℂ) ^ s
  have hm : Measurable f := Complex.measurable_ofReal.pow_const s
  have hf (x : ℝ) (hx : 0 < x) : ‖f x‖ ≤ 1 * x ^ s.re := by
    rw [one_mul]
    exact (Complex.norm_cpow_eq_rpow_re_of_pos hx s).le
  exact hI f f s.re s.re 1 1 ((le_max_left _ _).trans hs) ((le_max_right _ _).trans hs) hm hm hf hf

end Langlands.Global.RankinSelbergGlobal.RealGapDualPowerMoment
