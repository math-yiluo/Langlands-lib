import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.Classification.Tempered
import Mathlib.Analysis.Calculus.FDeriv.Defs

/-!
# Square-integrable equal-rank JPSS integrals on the sharp half-plane

This proposition states absolute convergence and holomorphy of the actual
coefficient-model integrals on `Re(s) > 0`. It is not a proof of either claim.
The holomorphy formulation is derived from the normal convergence asserted in
JPSS Section 8.3; see the paired Markdown for the source boundary.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

/-- The equal-rank part of JPSS Section 8.3: square-integrable irreducible
representations give absolutely convergent, holomorphic coefficient-model
integrals on `Re(s) > 0`, for every compatible quotient measure. -/
def SquareIntegrableEqualRankAnalyticStatement : Prop :=
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
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
        Representation.IsIrreducible π → T.IsSquareIntegrable π →
        Representation.IsIrreducible σ → T.IsSquareIntegrable σ →
        ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ),
        ∀ f : (coefficientModel π ℓ).toSubmodule,
        ∀ f' : (coefficientModel σ ℓ').toSubmodule,
        ∀ Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier),
          (∀ s : ℂ, 0 < s.re →
            EqualRankConverges ψ (normalizedAbsoluteValue T) μ f.val f'.val Φ s) ∧
          DifferentiableOn ℂ
            (equalRankModelIntegral ψ (normalizedAbsoluteValue T) μ π σ ℓ ℓ' f f' Φ)
            {s : ℂ | 0 < s.re}

end Langlands.RankinSelberg
