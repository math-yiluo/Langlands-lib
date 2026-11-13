import Langlands.Representation.RankinSelberg.FiniteFunctionShellSeriesStatement
import Langlands.AllField.LocalField.Foundation
/-!
# Shell generating integrals of finite functions

A derived internal proposition target for the valuation-shell route to the
one-variable Mellin argument of JPSS (1983), printed pages 391–392. The
coefficients are actual integrals over the integral units; one recurrence
and one convergence bound serve every Schwartz--Bruhat test function.
No analytic assertion is proved here.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding FiniteFunctionShellSeriesStatement
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.HarmonicAnalysis

universe uF

/-- Actual shell coefficients have a lower support bound and a uniformly
recurrent tail. On one punctured disc, uniform over the full Schwartz--Bruhat
space, their bilateral generating sum equals the actual integrable Haar
integral weighted by the integer power of the normalized order. -/
def FiniteFunctionShellSeriesStatement : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI := borel Fˣ
    letI : BorelSpace Fˣ := ⟨rfl⟩
    ∀ (η : Fˣ → ℂ), Continuous η →
      FiniteDimensional ℂ (Submodule.span ℂ
        (Set.range fun b : Fˣ => fun a : Fˣ => η (b * a))) →
      let μ : Measure Fˣ := localMultiplicativeHaar F
      let K : Set Fˣ :=
        (integralUnits (ValuativeRel.valuation F).integer : Set Fˣ)
      ∃ (π : Fˣ) (E : LinearRecurrence ℂ) (B : ℝ),
        T.ord (π : F) = 1 ∧ 1 ≤ B ∧
        ∀ Φ : SchwartzBruhat F,
          let c : ℤ → ℂ := fun n =>
            ∫ u in K, Φ ((π ^ n * u : Fˣ) : F) *
              η (π ^ n * u) ∂μ
          ∃ (L : ℤ) (N : ℕ), L ≤ (N : ℤ) ∧
            (∀ n : ℤ, n < L → c n = 0) ∧
            E.IsSolution (fun j : ℕ => c ((j : ℤ) + (N : ℤ))) ∧
            ∀ z : ℂ, z ≠ 0 → B * ‖z‖ < 1 →
              Integrable (fun a : Fˣ =>
                Φ (a : F) * η a * z ^ (T.ord (a : F))) μ ∧
              Summable (fun n : ℤ => c n * z ^ n) ∧
              (∫ a : Fˣ,
                Φ (a : F) * η a * z ^ (T.ord (a : F)) ∂μ) =
                ∑' n : ℤ, c n * z ^ n

end Langlands.AllField.RankinSelberg
