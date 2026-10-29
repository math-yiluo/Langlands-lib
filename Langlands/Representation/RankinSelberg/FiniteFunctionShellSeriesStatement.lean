import Langlands.HarmonicAnalysis.Basic
import Langlands.LocalField.Normalization.Definitions
import Langlands.Representation.RankinSelberg.Measures
import Mathlib.Algebra.LinearRecurrence
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Shell generating integrals of finite functions

A derived internal proposition target for the valuation-shell route to the
one-variable Mellin argument of JPSS (1983), printed pages 391–392. The
coefficients are actual integrals over the integral units; one recurrence
and one convergence bound serve every Schwartz--Bruhat test function.
No analytic assertion is proved here.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis

universe uF

/-- Actual shell coefficients have a lower support bound and a uniformly
recurrent tail. On one punctured disc, uniform over the full Schwartz--Bruhat
space, their bilateral generating sum equals the actual integrable Haar
integral weighted by the integer power of the normalized order. -/
def FiniteFunctionShellSeriesStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p)
    (T : F.TopologicalData),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel F.Carrierˣ
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    ∀ (η : F.Carrierˣ → ℂ), Continuous η →
      FiniteDimensional ℂ (Submodule.span ℂ
        (Set.range fun b : F.Carrierˣ => fun a : F.Carrierˣ => η (b * a))) →
      let μ : Measure F.Carrierˣ := localMultiplicativeHaar F.Carrier
      let K : Set F.Carrierˣ :=
        (integralUnits (ValuativeRel.valuation F.Carrier).integer : Set F.Carrierˣ)
      ∃ (π : F.Carrierˣ) (E : LinearRecurrence ℂ) (B : ℝ),
        T.ord (π : F.Carrier) = 1 ∧ 1 ≤ B ∧
        ∀ Φ : SchwartzBruhat F.Carrier,
          let c : ℤ → ℂ := fun n =>
            ∫ u in K, Φ ((π ^ n * u : F.Carrierˣ) : F.Carrier) *
              η (π ^ n * u) ∂μ
          ∃ (L : ℤ) (N : ℕ), L ≤ (N : ℤ) ∧
            (∀ n : ℤ, n < L → c n = 0) ∧
            E.IsSolution (fun j : ℕ => c ((j : ℤ) + (N : ℤ))) ∧
            ∀ z : ℂ, z ≠ 0 → B * ‖z‖ < 1 →
              Integrable (fun a : F.Carrierˣ =>
                Φ (a : F.Carrier) * η a * z ^ (T.ord (a : F.Carrier))) μ ∧
              Summable (fun n : ℤ => c n * z ^ n) ∧
              (∫ a : F.Carrierˣ,
                Φ (a : F.Carrier) * η a * z ^ (T.ord (a : F.Carrier)) ∂μ) =
                ∑' n : ℤ, c n * z ^ n

end Langlands.RankinSelberg
