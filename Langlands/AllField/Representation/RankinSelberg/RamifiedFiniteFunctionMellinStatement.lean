import Langlands.Representation.RankinSelberg.RamifiedFiniteFunctionMellinStatement
import Langlands.AllField.HarmonicAnalysis.ConductorSupplement
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

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding RamifiedFiniteFunctionMellinStatement
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis

universe uF

/-- A sufficiently ramified twist of a continuous translation-finite function
has convergent weighted Mellin integrals with Laurent polynomial continuation.
The ramification threshold depends only on the field data and finite function. -/
def RamifiedFiniteFunctionMellinStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI := borel Fˣ
    letI : BorelSpace Fˣ := ⟨rfl⟩
    let dmu : Measure Fˣ := localMultiplicativeHaar F
    let finiteFunction := fun η : Fˣ → ℂ =>
      Continuous η ∧
        FiniteDimensional ℂ (Submodule.span ℂ
          (Set.range fun b : Fˣ => fun a : Fˣ => η (b * a)))
    ∀ η : Fˣ → ℂ, finiteFunction η →
      ∃ b : ℕ, ∀ α : Quasicharacter F,
        (∃ u ∈ T.principalUnits b, α u ≠ 1) →
        ∀ m : ℕ, 0 < m →
          ∀ Φ : SchwartzBruhat F,
            let f := fun (s : ℂ) (a : Fˣ) =>
              Φ (a : F) * η a * (α a : ℂ) *
                (T.normalizedAbs (a : F) : ℂ) ^ ((m : ℂ) * s)
            let mellin := fun s : ℂ => ∫ a : Fˣ, f s a ∂dmu
            (∃ c : ℝ, ∀ s : ℂ, c < s.re → Integrable (f s) dmu) ∧
            (∃ L : LaurentCoefficients,
              HasRationalContinuation T.residueCardinality mellin (laurentToRatFunc L))

end Langlands.AllField.RankinSelberg
