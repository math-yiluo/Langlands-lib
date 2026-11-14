import Langlands.Representation.RankinSelberg.UniformFiniteFunctionMellinConvergenceStatement
import Langlands.AllField.Representation.RankinSelberg.FiniteFunctionMellinStatement
/-!
# A test-independent Mellin convergence threshold

This internal strengthening isolates only the convergence quantifier needed by
common matrix convergence. Rational continuations and a common denominator are
already supplied by the published finite-function Mellin theorem.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding FiniteFunctionMellinStatement UniformFiniteFunctionMellinConvergenceStatement
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open scoped BigOperators

universe uF

/-- For a fixed finite family of continuous translation-finite torus functions,
one right half-plane works for every Schwartz--Bruhat test function. -/
def UniformFiniteFunctionMellinConvergenceStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI := borel Fˣ
    letI : BorelSpace Fˣ := ⟨rfl⟩
    ∀ (r : ℕ) (m : Fin r → ℕ), (∀ i, 0 < m i) →
      let A := Fin r → Fˣ
      let dA : Measure A := Measure.pi (fun _ : Fin r => localMultiplicativeHaar F)
      let finiteFunction := fun η : A → ℂ =>
        Continuous η ∧
          FiniteDimensional ℂ (Submodule.span ℂ
            (Set.range fun b : A => fun a : A => η (b * a)))
      let integrand := fun (η : A → ℂ) (Φ : SchwartzBruhat (Fin r → F))
          (s : ℂ) (a : A) =>
        Φ (fun i => (a i : F)) * η a *
          ∏ i : Fin r, (T.normalizedAbs (a i : F) : ℂ) ^ ((m i : ℂ) * s)
      ∀ X : Finset (A → ℂ), (∀ η ∈ X, finiteFunction η) →
        ∃ c : ℝ, ∀ η ∈ X, ∀ Φ : SchwartzBruhat (Fin r → F),
          ∀ s : ℂ, c < s.re → Integrable (integrand η Φ s) dA

end Langlands.AllField.RankinSelberg
