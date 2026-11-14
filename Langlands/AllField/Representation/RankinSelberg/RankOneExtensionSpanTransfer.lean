import Langlands.Representation.RankinSelberg.RankOneExtensionSpanTransfer
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionAnalyticData
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionSpanComparisonStatement
/-!
# Transfer layer for the strict rank-one extension span comparison

The bookkeeping half of JPSS (1983), Lemma (5.5): from a pointwise identity
`Ψ_ind(s) = c Ψ_base(s)`, with `c ≠ 0` and the induced integral absolutely
convergent on a right half-plane, deduce the inclusion of the Laurent spans of
the actual zeta values. The rank equations of `unequalRankZetaValuesAt` are
unpacked through an explicit rank cast of Whittaker functions, and the casts are
evaluated on the concrete block matrices of `RankOneExtensionAnalyticData`.
No analytic comparison is proved here.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement RankOneExtensionLDivisibilityStatement RankOneExtensionSpanComparisonStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneExtensionLowerFamily rankOneExtensionLowerInduced rankOneExtensionLowerModel rankOneExtensionLowerSection rankOneExtensionLowerSectionCoefficient rankOneExtensionLowerSectionEval rankOneExtensionLowerToUpperEquiv rankOneExtensionSpanComparison_of_pointwise rankOneExtensionWhittakerContraction rankOneWhittakerType
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding functionalsCongr
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW uW₂

section RankCast


end RankCast

section ZetaValues


end ZetaValues

section SpanGlue

end SpanGlue

section PointwiseTransfer


end PointwiseTransfer

section StatementShape

/-- The transfer in the shape of `RankOneExtensionSpanComparisonStatement`, with the
trailing index `k` and both rank equations arbitrary; the statement is the instance
`k = r - t - 2` with its proofs `hrBase` and `hrInd`. The only extra premise is the
pointwise comparison of the actual zeta integrals: every convergent block-one
integral of `π × σ₁` is, on a right half-plane, a nonzero constant multiple of an
absolutely convergent block-zero integral of `π` against the lower induction. -/
theorem rankOneExtensionSpanComparison_of_pointwise
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (r t k : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ₁ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)
    (χ : Quasicharacter F)
    (hrB : r = t + (1 + k + 1)) (hrI : r = (1 + t) + (0 + k + 1)) :
    let χlift : Representation ℂ (Langlands.GeneralLinear 1 F)
        (ULift.{uW} ℂ) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp
        (rankOneCharacter (χ : Fˣ →* ℂˣ))
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (t + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (t + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (t + 1) F)
    letI : BorelSpace (upperUnipotent (t + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient t F)
    letI : BorelSpace (LeftUnipotentQuotient t F) := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear ((1 + t) + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear ((1 + t) + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent ((1 + t) + 1) F)
    letI : BorelSpace (upperUnipotent ((1 + t) + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient (1 + t) F)
    letI : BorelSpace (LeftUnipotentQuotient (1 + t) F) := ⟨rfl⟩
    ∀ (μbase : Measure (LeftUnipotentQuotient t F))
      (μind : Measure (LeftUnipotentQuotient (1 + t) F)),
      (∀ W₀ ∈ whittakerSet ψ r π, ∀ W' ∈ inverseWhittakerSet ψ t σ₁,
        (∃ a : ℝ, ∀ s : ℂ, a < s.re →
          UnequalRankConverges ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) 1 k
            μbase (rectangularMeasure ν.val 1 (t + 1)) (rankCastWhittaker ψ hrB W₀) W' s) →
        ∃ W₁ ∈ whittakerSet ψ r π,
          ∃ W'' ∈ inverseWhittakerSet ψ (1 + t) (rankOneExtensionLowerInduced F t χlift σ₁),
          ∃ c : ℂ, c ≠ 0 ∧ ∃ a' : ℝ, ∀ s : ℂ, a' < s.re →
            UnequalRankConverges ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) 0 k
              μind (rectangularMeasure ν.val 0 ((1 + t) + 1))
              (rankCastWhittaker ψ hrI W₁) W'' s ∧
            unequalRankIntegral ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) 0 k
                μind (rectangularMeasure ν.val 0 ((1 + t) + 1))
                (rankCastWhittaker ψ hrI W₁) W'' s =
              c * unequalRankIntegral ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
                1 k μbase (rectangularMeasure ν.val 1 (t + 1))
                (rankCastWhittaker ψ hrB W₀) W' s) →
      zetaSpan (unequalRankZetaValuesAt (r := r) (n := t) 1 k hrB
        (⟨⟩ : LocalFieldData F).residueCardinality ψ
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μbase
        (rectangularMeasure ν.val 1 (t + 1)) π σ₁) ≤
      zetaSpan (unequalRankZetaValuesAt (r := r) (n := 1 + t) 0 k hrI
        (⟨⟩ : LocalFieldData F).residueCardinality ψ
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μind
        (rectangularMeasure ν.val 0 ((1 + t) + 1)) π
        (rankOneExtensionLowerInduced F t χlift σ₁)) := by
  intro χlift
  let := borel F
  let := borel (LeftUnipotentQuotient t F)
  let := borel (LeftUnipotentQuotient (1 + t) F)
  intro μbase μind H
  exact zetaSpan_unequalRankZetaValuesAt_le_of_pointwise 1 k 0 k hrB hrI
    (⟨⟩ : LocalFieldData F).residueCardinality ψ
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μbase μind
    (rectangularMeasure ν.val 1 (t + 1)) (rectangularMeasure ν.val 0 ((1 + t) + 1)) π σ₁
    _ H

end StatementShape

section Matrices


end Matrices

section Integrands



end Integrands

end Langlands.AllField.RankinSelberg
