import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.RankinSelberg.WhittakerNormData
import Langlands.Representation.Classification.Tempered

/-!
# The square-integrable Whittaker restriction-square estimate

JPSS Section 8.3, formula (7) on printed page 450: the square of a restricted
Whittaker function of a square-integrable representation, weighted by the
determinant power `-(r - t)`, is integrable on `N_t \ G_t`. This module defines
a proposition; it does not prove it.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

/-- For an irreducible square-integrable representation of
`GL_(n + (0 + k + 1) + 1)`, every coefficient-model vector has integrable
restricted Whittaker square weighted by `|det g| ^ (-(k + 1))` on
`N_(n+1) \ GL_(n+1)`, for every supplied compatible quotient measure.
Square-integrability is the analytic predicate modulo the center for the
supplied topology. -/
def SquareIntegrableWhittakerRestrictionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n k : ℕ),
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel F.Carrier
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
      ∀ π : Representation ℂ
          (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier) V,
        Representation.IsIrreducible π → T.IsSquareIntegrable π →
        ∀ (ℓ : glFunctionals ψ (n + (0 + k + 1)) π)
          (f : (coefficientModel π ℓ).toSubmodule),
          Integrable
            (fun q : LeftUnipotentQuotient n F.Carrier =>
              restrictedWhittakerNorm ψ k f.val q ^ 2 *
                quotientDeterminantAbs (normalizedAbsoluteValue T) n q ^
                  (-(((0 + k + 1 : ℕ) : ℝ)))) μ

end Langlands.RankinSelberg
