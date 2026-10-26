import Langlands.HarmonicAnalysis.Basic
import Langlands.LocalField.Normalization.Definitions
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.RankinSelberg.RationalContinuation
import Langlands.Representation.RankinSelberg.RationalZeta
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Weighted one-variable Mellin integrals of finite functions

A proposition target derived from JPSS (1983), printed page 392, display (6)
and the following paragraphs. The common denominator is uniform over the
entire Schwartz--Bruhat space for a fixed continuous translation-finite
function and positive integral weight. No analytic conclusion is proved here.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis

universe uF

/-- Actual convergence, rational continuation in `q^(-s)`, and one common
Laurent denominator for the weighted Mellin integrals of a finite function.
All auxiliary functions and sets are local to this proposition. -/
def OneVariableMellinStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p)
    (T : F.TopologicalData),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel F.Carrierˣ
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    ∀ (m : ℕ), 0 < m →
      ∀ (η : F.Carrierˣ → ℂ), Continuous η →
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : F.Carrierˣ => fun a : F.Carrierˣ => η (b * a))) →
        let dA : Measure F.Carrierˣ := localMultiplicativeHaar F.Carrier
        let integrand := fun (Φ : SchwartzBruhat F.Carrier) (s : ℂ)
            (a : F.Carrierˣ) =>
          Φ (a : F.Carrier) * η a *
            (T.normalizedAbs (a : F.Carrier) : ℂ) ^ ((m : ℂ) * s)
        let mellin := fun (Φ : SchwartzBruhat F.Carrier) (s : ℂ) =>
          ∫ a : F.Carrierˣ, integrand Φ s a ∂dA
        let rationalValues : Set RationalFunctions :=
          {R | ∃ Φ : SchwartzBruhat F.Carrier,
            HasRationalContinuation T.residueCardinality (mellin Φ) R}
        (∀ Φ : SchwartzBruhat F.Carrier,
          ∃ c : ℝ, ∀ s : ℂ, c < s.re → Integrable (integrand Φ s) dA) ∧
        (∀ Φ : SchwartzBruhat F.Carrier,
          ∃ R : RationalFunctions,
            HasRationalContinuation T.residueCardinality (mellin Φ) R) ∧
        HasCommonDenominator rationalValues

end Langlands.RankinSelberg
