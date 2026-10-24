import Langlands.HarmonicAnalysis.Basic
import Langlands.LocalField.Normalization.Definitions
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.RankinSelberg.RationalContinuation
import Langlands.Representation.RankinSelberg.RationalZeta
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Mellin integrals of finite functions on a p-adic torus

A proposition target derived from the tensor reduction and one-variable Mellin
argument in JPSS (1983), printed page 392, displays (5)-(6). The denominator is
uniform over all Schwartz--Bruhat test functions for a fixed finite family of
translation-finite functions. No analytic conclusion is assumed or proved here.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis
open scoped BigOperators

universe uF

/-- Convergence, rational continuation in `q^(-s)`, and a common Laurent
polynomial denominator for a finite family of finite functions on `(Fˣ)^r`.
The positive integral weights include the JPSS weights `m i = i.val + 1`.
All auxiliary functions and sets below are local to this proposition. -/
def FiniteFunctionMellinStatement : Prop :=
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
      let mellin := fun (η : A → ℂ) (Φ : SchwartzBruhat (Fin r → F.Carrier))
          (s : ℂ) => ∫ a : A, integrand η Φ s a ∂dA
      ∀ X : Finset (A → ℂ), (∀ η ∈ X, finiteFunction η) →
        let rationalValues : Set RationalFunctions :=
          {R | ∃ η ∈ X, ∃ Φ : SchwartzBruhat (Fin r → F.Carrier),
            HasRationalContinuation T.residueCardinality (mellin η Φ) R}
        (∀ η ∈ X, ∀ Φ : SchwartzBruhat (Fin r → F.Carrier),
          ∃ c : ℝ, ∀ s : ℂ, c < s.re → Integrable (integrand η Φ s) dA) ∧
        (∀ η ∈ X, ∀ Φ : SchwartzBruhat (Fin r → F.Carrier),
          ∃ R : RationalFunctions,
            HasRationalContinuation T.residueCardinality (mellin η Φ) R) ∧
        HasCommonDenominator rationalValues

end Langlands.RankinSelberg
