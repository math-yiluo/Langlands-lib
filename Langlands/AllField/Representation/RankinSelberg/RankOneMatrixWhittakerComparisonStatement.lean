import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonStatement
import Langlands.AllField.Representation.GodementJacquet.Zeta
/-!
# Rank-one JPSS `I₁ = I₃`: character zeta values versus matrix–Whittaker integrals

The comparison `I₁ = I₃` of JPSS (1983), Section 5.2, printed 420–421, as an
equality of Laurent submodules of `RationalFunctions`, for every full
Whittaker-type representation of actual rank `n + 1` and every nonzero
standard Whittaker functional. This module only defines the proposition.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement RankOneMatrixWhittakerComparisonStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV

/-- JPSS (1983) Section 5.2, `I₁ = I₃` (from JPS 1979 Theorem 4.3 and Remark 4.2
when `n > 0`, and directly from the Tate/equal-rank integral when `n = 0`).
For `σ` of full Whittaker type on `GL_(n+1)` and a nonzero standard functional `ℓ`,
the Laurent span of the rank-one character zeta values of `σ × 1` equals the
Laurent span of the shifted Godement–Jacquet integrals of the coefficient model
of `ℓ`. Every compatible quotient measure on `N₁ \ GL₁` is quantified. -/
def RankOneMatrixWhittakerComparisonStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V),
    letI := borel (Langlands.GeneralLinear (0 + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (0 + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (0 + 1) F)
    letI : BorelSpace (upperUnipotent (0 + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient 0 F)
    letI : BorelSpace (LeftUnipotentQuotient 0 F) := ⟨rfl⟩
    IsOfWhittakerType n (standardCharacter ψ n) σ →
    ∀ ℓ : glFunctionals ψ n σ, ℓ.val ≠ 0 →
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F 0)],
    ∀ μ : Measure (LeftUnipotentQuotient 0 F),
      IsCompatible (upperUnipotent (0 + 1) F)
        (generalLinearHaar F 0) (unipotentHaar F 0) μ →
      zetaSpan (characterZetaValues (⟨⟩ : LocalFieldData F).residueCardinality ψ
          (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μ
          (1 : Fˣ →* ℂˣ) n σ) =
        Langlands.AllField.GodementJacquet.Padic.jpssI3 F ψ σ ℓ

end Langlands.AllField.RankinSelberg
