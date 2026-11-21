import Langlands.Global.RankinSelberg.ComplexGapDualHaar

/-! # Common product-determinant moments on the full dual chart -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapDualPowerMoment

open Langlands.Archimedean (unitaryCompact)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.RankinSelberg (rectangularMeasure)
open ArchimedeanLocal (ComplexQuotientMeasureData complexSelfDualMeasure)
open ComplexGapAlternateRestriction (GodementColumnFactors)
open ComplexGapDualHaar (dualChartMeasure dualChartWeightedKernel complexGapDualHaarPowerBounds)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

variable (t q : ℕ)
local notation "k" => t + 1
local notation "r" => t + 1 + q
local notation "n" => t + 1 + q + 1
local notation "Test" => 𝓢(Matrix (Fin n) (Fin (n + 1)) ℂ, ℂ)

/-- The unintegrated dual chart admits the same complex Mellin power in both determinant
variables, on a sufficiently far right half-plane. -/
def ComplexGapDualPowerMomentStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData t) (a : ℂˣ) (κ : Measure (unitaryCompact ℂ n)),
    κ.IsHaarMeasure → κ.IsInvInvariant →
    ∀ (ds es : List ComplexCharacterData) (Wd : complexWhittakerModel r ds a)
      (Vd : complexWhittakerModel t es (-a)) (d : ComplexCharacterData) (Φ : Test)
      (T : GodementColumnFactors k q), (∀ x, Φ x = T.eval k q x) →
    ∃ σ : ℝ, ∀ s : ℂ, σ ≤ s.re →
      Integrable (dualChartWeightedKernel t q a d Φ Wd.val Vd.val 0
        (fun x : ℝ => (x : ℂ) ^ s) (fun x : ℝ => (x : ℂ) ^ s))
        (D.measure.prod ((rectangularMeasure (complexSelfDualMeasure a) (n - k) k).prod (dualChartMeasure t q a κ)))

theorem complexGapDualPowerMoment : ComplexGapDualPowerMomentStatement t q := by
  intro D a κ hκ hκinv ds es Wd Vd d Φ T hT
  obtain ⟨α, γ, hI⟩ := complexGapDualHaarPowerBounds t q D a κ hκ hκinv ds es Wd Vd d Φ T hT 0
  refine ⟨max α γ, ?_⟩
  intro s hs
  let f (x : ℝ) := (x : ℂ) ^ s
  have hm : Measurable f := Complex.measurable_ofReal.pow_const s
  have hf (x : ℝ) (hx : 0 < x) : ‖f x‖ ≤ 1 * x ^ s.re := by
    rw [one_mul]
    exact (Complex.norm_cpow_eq_rpow_re_of_pos hx s).le
  exact hI f f s.re s.re 1 1 ((le_max_left _ _).trans hs) ((le_max_right _ _).trans hs) hm hm hf hf

end Langlands.Global.RankinSelbergGlobal.ComplexGapDualPowerMoment
