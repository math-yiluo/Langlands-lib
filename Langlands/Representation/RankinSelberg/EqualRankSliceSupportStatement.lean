import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.RankinSelberg.DeterminantSlices
import Langlands.HarmonicAnalysis.BilateralLaurentSeries

/-!
# Equal-rank determinant-slice lower support

The finite negative tail of JPSS (1983), Section 4.2, printed page 407,
for actual coefficient images of full Whittaker-type representations.
This is a proposition definition; no support or convergence proof is supplied.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

/-- The equal-rank slice coefficients have support bounded below for every
pair of full Whittaker-type representations and every coefficient and test
function. Zero functionals and coefficients, and actual rank one, are included. -/
def EqualRankSliceSupportStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
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
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
        IsOfWhittakerType n (standardCharacter ψ n) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
        ∀ (f : (coefficientModel π ℓ).toSubmodule)
          (f' : (coefficientModel σ ℓ').toSubmodule)
          (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
          BilateralLaurentSeries.HasLowerBoundedSupport
            (equalRankSliceCoefficient T μ ψ f.val f'.val Φ)

end Langlands.RankinSelberg
