import Langlands.HarmonicAnalysis.Conductor
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.RankinSelberg.RationalContinuation
import Langlands.Representation.RankinSelberg.RationalZeta
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Uniform ramified Laurentness of scalar finite-function Mellin integrals

A proposition target derived from the scalar Mellin argument on printed
page 392 and the ramification argument in Proposition (2.13), printed
page 404, of JPSS (1983). The unit threshold precedes every twisting
quasicharacter, positive integral weight and Schwartz--Bruhat test.
Actual convergence and Laurent continuation are asserted together.
No analytic conclusion is proved here.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis

universe uF

/-- A sufficiently ramified twist of a continuous translation-finite function
has convergent weighted Mellin integrals with Laurent polynomial continuation.
The ramification threshold depends only on the field data and finite function. -/
def RamifiedFiniteFunctionMellinStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p)
    (T : F.TopologicalData),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel F.Carrierˣ
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    let dmu : Measure F.Carrierˣ := localMultiplicativeHaar F.Carrier
    let finiteFunction := fun η : F.Carrierˣ → ℂ =>
      Continuous η ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : F.Carrierˣ => fun a : F.Carrierˣ => η (b * a)))
    ∀ η : F.Carrierˣ → ℂ, finiteFunction η →
      ∃ b : ℕ, ∀ α : Quasicharacter F.Carrier,
        (∃ u ∈ T.principalUnits b, α u ≠ 1) →
        ∀ m : ℕ, 0 < m →
          ∀ Φ : SchwartzBruhat F.Carrier,
            let f := fun (s : ℂ) (a : F.Carrierˣ) =>
              Φ (a : F.Carrier) * η a * (α a : ℂ) *
                (T.normalizedAbs (a : F.Carrier) : ℂ) ^ ((m : ℂ) * s)
            let mellin := fun s : ℂ => ∫ a : F.Carrierˣ, f s a ∂dmu
            (∃ c : ℝ, ∀ s : ℂ, c < s.re → Integrable (f s) dmu) ∧
            (∃ L : LaurentCoefficients,
              HasRationalContinuation T.residueCardinality mellin (laurentToRatFunc L))

end Langlands.RankinSelberg
