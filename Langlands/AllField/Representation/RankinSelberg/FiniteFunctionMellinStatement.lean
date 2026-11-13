import Langlands.Representation.RankinSelberg.FiniteFunctionMellinStatement
import Langlands.AllField.LocalField.Foundation
/-!
# Mellin integrals of finite functions on a torus over a nonarchimedean local field

A proposition target derived from the tensor reduction and one-variable Mellin
argument in JPSS (1983), printed page 392, displays (5)-(6). The denominator is
uniform over all Schwartz--Bruhat test functions for a fixed finite family of
translation-finite functions. No analytic conclusion is assumed or proved here.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding FiniteFunctionMellinStatement
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.HarmonicAnalysis
open scoped BigOperators

universe uF

/-- Convergence, rational continuation in `q^(-s)`, and a common Laurent
polynomial denominator for a finite family of finite functions on `(Fˣ)^r`.
The positive integral weights include the JPSS weights `m i = i.val + 1`.
All auxiliary functions and sets below are local to this proposition. -/
def FiniteFunctionMellinStatement : Prop :=
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
      let mellin := fun (η : A → ℂ) (Φ : SchwartzBruhat (Fin r → F))
          (s : ℂ) => ∫ a : A, integrand η Φ s a ∂dA
      ∀ X : Finset (A → ℂ), (∀ η ∈ X, finiteFunction η) →
        let rationalValues : Set RationalFunctions :=
          {R | ∃ η ∈ X, ∃ Φ : SchwartzBruhat (Fin r → F),
            HasRationalContinuation T.residueCardinality (mellin η Φ) R}
        (∀ η ∈ X, ∀ Φ : SchwartzBruhat (Fin r → F),
          ∃ c : ℝ, ∀ s : ℂ, c < s.re → Integrable (integrand η Φ s) dA) ∧
        (∀ η ∈ X, ∀ Φ : SchwartzBruhat (Fin r → F),
          ∃ R : RationalFunctions,
            HasRationalContinuation T.residueCardinality (mellin η Φ) R) ∧
        HasCommonDenominator rationalValues

end Langlands.AllField.RankinSelberg
