import Langlands.BaseChange.OrbitalIntegral
import Langlands.HarmonicAnalysis.Basic
import Langlands.TraceFormula.TwistedOrbital
import Langlands.Analysis.Local.QuotientMeasure
import Mathlib.Analysis.Complex.Order
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Statement: positivity of orbital integrals

For a nonarchimedean local field `F` of characteristic zero, a Haar measure `μF` on `GL_n(F)`,
a nonnegative test function `f` and a regular semisimple `γ` with `f γ > 0`: the orbital
integral of `f` at `γ` is positive for every right Haar measure on the centralizer `G_γ(F)` and
every compatible quotient measure on `G_γ(F) \ GL_n(F)` (Henniart–Lemaire 2011, II.6.8, printed
p. 124: `Λ(f_v, γ) > 0`). The statement is not proved here. See the paired Markdown.
-/

noncomputable section

open MeasureTheory

namespace Langlands.BaseChange

open HarmonicAnalysis (SchwartzBruhat)

universe u

open scoped ComplexOrder in
/-- Positivity of orbital integrals (Henniart–Lemaire, II.6.8): for a Haar measure `μF` on
`GL_n(F)`, a test function `f ≥ 0` and a regular semisimple `γ` with `f γ > 0`, the orbital
integral `∫ f(x⁻¹ γ x) dνγ(x)` over `G_γ(F) \ GL_n(F)` is positive for every right Haar measure
`μγ` on `G_γ(F)` and every quotient measure `νγ` compatible with `μF / μγ`. -/
def OrbitalIntegralPositivityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (n : ℕ),
    letI : MeasurableSpace (GeneralLinear n F) := borel _
    ∀ (μF : Measure (GeneralLinear n F)), μF.IsHaarMeasure →
    ∀ (f : SchwartzBruhat (GeneralLinear n F)) (γ : GeneralLinear n F),
      JacquetLanglands.IsRegularSemisimple γ → (∀ g, 0 ≤ f g) → 0 < f γ →
      haveI : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
      letI : MeasurableSpace (QuotientIntegration.LeftQuotient (glCentralizer γ)) := borel _
      haveI : BorelSpace (QuotientIntegration.LeftQuotient (glCentralizer γ)) := ⟨rfl⟩
      ∀ (μγ : Measure (glCentralizer γ)) [μγ.IsHaarMeasure] [μγ.IsMulRightInvariant]
        (νγ : Measure (QuotientIntegration.LeftQuotient (glCentralizer γ))),
        QuotientIntegration.IsCompatible (glCentralizer γ) μF μγ νγ →
        0 < Langlands.TraceFormula.orbitalIntegral γ νγ (f : GeneralLinear n F → ℂ)

end Langlands.BaseChange
