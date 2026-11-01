import Langlands.Representation.RankinSelberg.FiniteFunctionMellinStatement

/-!
# A test-independent Mellin convergence threshold

This internal strengthening isolates only the convergence quantifier needed by
common matrix convergence. Rational continuations and a common denominator are
already supplied by the published finite-function Mellin theorem.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis
open scoped BigOperators

universe uF

/-- For a fixed finite family of continuous translation-finite torus functions,
one right half-plane works for every Schwartz--Bruhat test function. -/
def UniformFiniteFunctionMellinConvergenceStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p)
    (T : F.TopologicalData),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel F.Carrierˣ
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    ∀ (r : ℕ) (m : Fin r → ℕ), (∀ i, 0 < m i) →
      let A := Fin r → F.Carrierˣ
      let dA : Measure A := Measure.pi (fun _ : Fin r => localMultiplicativeHaar F.Carrier)
      let finiteFunction := fun η : A → ℂ =>
        Continuous η ∧
          FiniteDimensional ℂ (Submodule.span ℂ
            (Set.range fun b : A => fun a : A => η (b * a)))
      let integrand := fun (η : A → ℂ) (Φ : SchwartzBruhat (Fin r → F.Carrier))
          (s : ℂ) (a : A) =>
        Φ (fun i => (a i : F.Carrier)) * η a *
          ∏ i : Fin r, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^ ((m i : ℂ) * s)
      ∀ X : Finset (A → ℂ), (∀ η ∈ X, finiteFunction η) →
        ∃ c : ℝ, ∀ η ∈ X, ∀ Φ : SchwartzBruhat (Fin r → F.Carrier),
          ∀ s : ℂ, c < s.re → Integrable (integrand η Φ s) dA

end Langlands.RankinSelberg
