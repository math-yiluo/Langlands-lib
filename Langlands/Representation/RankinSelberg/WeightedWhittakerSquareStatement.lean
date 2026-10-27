import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.RankinSelberg.WhittakerNormData
import Langlands.Representation.Classification.Tempered

/-!
# Weighted Whittaker square estimates for square-integrable representations

This proposition states, for both character signs, integrability on the actual
left-unipotent quotient of the squared Whittaker norm weighted by a squared
Schwartz–Bruhat factor and a positive determinant power. It is a derived
single-representation specialization of the equal-rank case of JPSS Section 8.3,
not a proof of it; see the paired Markdown for the source boundary.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

/-- For an irreducible square-integrable representation, every coefficient-model
vector for either Whittaker character sign has an integrable weighted square
`|W(g)|² |Φ(e_{n+1} g)|² |det g|^{2a}` on `N_(n+1) \ GL_(n+1)` for every `a > 0`
and every compatible quotient measure. The first conjunct uses the standard
character, the second the inverse character. -/
def WeightedWhittakerSquareStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ),
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
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
      ∀ π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V,
        Representation.IsIrreducible π → T.IsSquareIntegrable π →
        (∀ (ℓ : glFunctionals ψ n π) (f : (coefficientModel π ℓ).toSubmodule)
            (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)) (a : ℝ), 0 < a →
          Integrable (fun q => (whittakerNorm ψ f.val q) ^ 2 *
              ‖Φ (quotientLastRow n q)‖ ^ 2 *
              (quotientDeterminantAbs (normalizedAbsoluteValue T) n q) ^ (2 * a)) μ) ∧
        (∀ (ℓ : glInverseFunctionals ψ n π) (f : (coefficientModel π ℓ).toSubmodule)
            (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)) (a : ℝ), 0 < a →
          Integrable (fun q => (inverseWhittakerNorm ψ f.val q) ^ 2 *
              ‖Φ (quotientLastRow n q)‖ ^ 2 *
              (quotientDeterminantAbs (normalizedAbsoluteValue T) n q) ^ (2 * a)) μ)

end Langlands.RankinSelberg
