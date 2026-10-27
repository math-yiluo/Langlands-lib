import Langlands.Representation.RankinSelberg.UnequalRankAnalyticExtraction
import Langlands.Representation.RankinSelberg.DualWhittakerType

/-!
# Conditional universal assembly of the block-zero gamma statement

The input consists of the three remaining universal proof obligations.
The assembly derives the dual Whittaker hypotheses and specializes the
actual analytic inputs; it does not prove those three obligations.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

/-- Exact universal inputs sufficient for the block-zero gamma assembly.
This proposition packages open proof obligations and does not assert them. -/
def UnequalRankBlockZeroGammaAssemblyInput {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n r : ℕ) : Prop :=
  (∀ j k, UnequalRankAnalyticStatement.{uF,uV,uW} F T n j k) ∧
  UnequalRankBlockZeroContinuedFormsStatement.{uF,uV,uW} F T n r ∧
  UnequalRankBilinearUniquenessStatement.{uF,uV,uW} F T n r

/-- Discharge the universal assembly once its three actual statement proofs
are supplied. No additional dual-type, nonvanishing or comparison hypothesis
is needed. The unconditional target remains open until these inputs are proved. -/
theorem UnequalRankBlockZeroGammaAssemblyInput.gammaExistence
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n r : ℕ) (h : UnequalRankBlockZeroGammaAssemblyInput.{uF,uV,uW} F T n r) :
    UnequalRankBlockZeroGammaExistenceStatement.{uF,uV,uW} F T n r := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  rcases h with ⟨hA, hforms, hunique⟩
  unfold UnequalRankBlockZeroGammaExistenceStatement
  intro hnr ψ hinv μ hμ ν _ V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ'
  have hπd : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r)
      (inverseTransposePullback π) := by
    simpa only [standardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback ψ π hπ
  have hσd : IsOfWhittakerType n (inverseStandardCharacter (ψ.scale (-1)) n)
      (inverseTransposePullback σ) := by
    simpa only [inverseStandardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback_inverse ψ σ hσ
  have hblocks : ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
      UnequalRankAnalyticAt j k hr T.residueCardinality ψ
        (normalizedAbsoluteValue T) μ (rectangularMeasure ν j (n + 1))
        π σ ℓ ℓ' := by
    intro j k hr
    subst r
    exact hA j k ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
  have hdualBlocks : ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
      UnequalRankAnalyticAt j k hr T.residueCardinality (ψ.scale (-1))
        (normalizedAbsoluteValue T) μ (rectangularMeasure ν j (n + 1))
        (inverseTransposePullback π) (inverseTransposePullback σ)
        (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ') := by
    intro j k hr
    subst r
    exact hA j k (ψ.scale (-1)) μ hμ ν V W
      (inverseTransposePullback π) (inverseTransposePullback σ)
      hπd hσd (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ')
      (firstDualFunctional_ne_zero ψ π hℓ) (secondDualFunctional_ne_zero ψ σ hℓ')
  exact exists_blockZeroGammaEquation_of_analytic T.residueCardinality_gt_one hσ
    (hblocks 0 (r - n - 1) (by omega))
    (hdualBlocks (r - n - 1) 0 (by omega))
    (hforms hnr ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
      (hblocks 0 (r - n - 1) (by omega))
      (hdualBlocks (r - n - 1) 0 (by omega)))
    (hunique hnr ψ V W π σ hπ hσ ℓ ℓ')

end Langlands.RankinSelberg
