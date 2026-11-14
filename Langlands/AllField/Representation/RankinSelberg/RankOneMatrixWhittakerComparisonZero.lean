import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonZero
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonStatement
/-!
# Rank-one `I₁ = I₃` at actual rank one

The `n = 0` branch of `RankOneMatrixWhittakerComparisonStatement`: a GL₁
equal-rank/Tate bridge. The subgroup `N₁` is trivial, so every compatible
quotient measure is the transported normalized Haar measure of `GL₁`; the
inverse Whittaker functions of the trivial character are the constants; vector
and `1 × 1` matrix test functions correspond through the last row; and the
complex shift `jpssShift 0` vanishes.

The file also proves two facts used by both branches: a nonzero standard
functional of a representation of Whittaker type gives the whole all-functional
Whittaker set, and at rank one every linear form is an inverse-character
functional.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement RankOneMatrixWhittakerComparisonStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneMatrixWhittakerComparison_zero
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV

section FunctionalLine


end FunctionalLine

section TestFunctions



end TestFunctions

section RankOneIntegrals



end RankOneIntegrals

section Comparison


end Comparison

section Padic

/-- The `n = 0` case of `RankOneMatrixWhittakerComparisonStatement`, in exactly the
form of the statement's body at `n = 0`. -/
theorem rankOneMatrixWhittakerComparison_zero 
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (0 + 1) F) V) :
    letI := borel (Langlands.GeneralLinear (0 + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (0 + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (0 + 1) F)
    letI : BorelSpace (upperUnipotent (0 + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient 0 F)
    letI : BorelSpace (LeftUnipotentQuotient 0 F) := ⟨rfl⟩
    IsOfWhittakerType 0 (standardCharacter ψ 0) σ →
    ∀ ℓ : glFunctionals ψ 0 σ, ℓ.val ≠ 0 →
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F 0)],
    ∀ μ : Measure (LeftUnipotentQuotient 0 F),
      IsCompatible (upperUnipotent (0 + 1) F)
        (generalLinearHaar F 0) (unipotentHaar F 0) μ →
      zetaSpan (characterZetaValues (⟨⟩ : LocalFieldData F).residueCardinality ψ
          (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μ
          (1 : Fˣ →* ℂˣ) 0 σ) =
        Langlands.AllField.GodementJacquet.Padic.jpssI3 F ψ σ ℓ := by
  intro hσ ℓ hℓ _ μ hμ
  let := borel (Langlands.GeneralLinear (0 + 1) F)
  have : BorelSpace (Langlands.GeneralLinear (0 + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (0 + 1) F)
  have : BorelSpace (upperUnipotent (0 + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient 0 F)
  have : BorelSpace (LeftUnipotentQuotient 0 F) := ⟨rfl⟩
  exact congrArg zetaSpan (characterZetaValues_one_zero_eq _ ψ _ hσ ℓ hℓ μ hμ)

end Padic

end Langlands.AllField.RankinSelberg
