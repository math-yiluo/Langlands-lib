import Langlands.Representation.RankinSelberg.OneVariableMellinStatement
import Langlands.AllField.LocalField.Foundation
/-!
# Weighted one-variable Mellin integrals of finite functions

A proposition target derived from JPSS (1983), printed page 392, display (6)
and the following paragraphs. The common denominator is uniform over the
entire Schwartz--Bruhat space for a fixed continuous translation-finite
function and positive integral weight. No analytic conclusion is proved here.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding OneVariableMellinStatement
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.HarmonicAnalysis

universe uF

/-- Actual convergence, rational continuation in `q^(-s)`, and one common
Laurent denominator for the weighted Mellin integrals of a finite function.
All auxiliary functions and sets are local to this proposition. -/
def OneVariableMellinStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI := borel Fˣ
    letI : BorelSpace Fˣ := ⟨rfl⟩
    ∀ (m : ℕ), 0 < m →
      ∀ (η : Fˣ → ℂ), Continuous η →
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : Fˣ => fun a : Fˣ => η (b * a))) →
        let dA : Measure Fˣ := localMultiplicativeHaar F
        let integrand := fun (Φ : SchwartzBruhat F) (s : ℂ)
            (a : Fˣ) =>
          Φ (a : F) * η a *
            (T.normalizedAbs (a : F) : ℂ) ^ ((m : ℂ) * s)
        let mellin := fun (Φ : SchwartzBruhat F) (s : ℂ) =>
          ∫ a : Fˣ, integrand Φ s a ∂dA
        let rationalValues : Set RationalFunctions :=
          {R | ∃ Φ : SchwartzBruhat F,
            HasRationalContinuation T.residueCardinality (mellin Φ) R}
        (∀ Φ : SchwartzBruhat F,
          ∃ c : ℝ, ∀ s : ℂ, c < s.re → Integrable (integrand Φ s) dA) ∧
        (∀ Φ : SchwartzBruhat F,
          ∃ R : RationalFunctions,
            HasRationalContinuation T.residueCardinality (mellin Φ) R) ∧
        HasCommonDenominator rationalValues

end Langlands.AllField.RankinSelberg
