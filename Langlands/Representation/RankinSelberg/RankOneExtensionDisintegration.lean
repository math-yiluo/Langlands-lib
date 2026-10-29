import Langlands.Representation.RankinSelberg.InducedTailIntermediateDisintegrationAdapters
import Langlands.Representation.RankinSelberg.RankOneExtensionUnfoldingMeasure
import Langlands.Representation.RankinSelberg.RankOneExtensionCellAlgebra

/-!
# Lower-block disintegration at the rank of the rank-one extension

The published lower-block chart `([g], x, h) ↦ [[[g,0],[x,h]]]` from
`N_(t+1) \ GL_(t+1) × M_(1×(t+1)) × B⁻_1` to `N_(t+2) \ GL_(t+2)`, with its target rank
written as `(1 + t) + 1`, and the specialization of `LowerBlockQuotientDisintegrationStatement`
to this chart (JPSS §9.3, printed 456, in the rank used by Lemma (5.5)).
-/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear QuotientIntegration MeasureTheory HarmonicAnalysis
  InducedTailIntermediate
open scoped ENNReal

universe uF

section Chart

variable {K : Type uF} [Field K] [TopologicalSpace K] {t : ℕ}

/-- The lower-block chart `([g], x, h) ↦ [[[g,0],[x,h]]]` of `N_(t+1) \ GL_(t+1)`,
followed by the rank equality `t + 1 + 1 = (1 + t) + 1` of its target quotient. -/
def rankOneExtensionQuotientChart
    (z : LeftUnipotentQuotient t K ×
      (Matrix (Fin 1) (Fin (t + 1)) K × lowerTriangularSubgroup 1 K)) :
    LeftUnipotentQuotient (1 + t) K :=
  upperUnipotentQuotientCongr (by omega : t + 1 + 1 = 1 + t + 1)
    (lowerBlockQuotientChart (a := t + 1) (d := 1) z)

/-- At a representative, the chart is the class of the lower block
`B(g, x, h₀₀) = [g, 0; x, h₀₀]` of `GL_(1+(t+1))`, read in rank `(1 + t) + 1`. -/
theorem rankOneExtensionQuotientChart_mk (hc : 1 + (t + 1) = (1 + t) + 1)
    (g : Langlands.GeneralLinear (t + 1) K) (x : Matrix (Fin 1) (Fin (t + 1)) K)
    (h : lowerTriangularSubgroup 1 K) :
    rankOneExtensionQuotientChart ((Quotient.mk _ g : LeftUnipotentQuotient t K), x, h) =
      Quotient.mk _ (reindex (R := K) (finCongr hc)
        (rankOneExtensionLowerBlock t g (x 0)
          (Units.mk0 (lowerScalarEntry h) (lowerScalarEntry_ne_zero h)))) := by
  simp only [rankOneExtensionQuotientChart, lowerBlockQuotientChart_mk,
    upperUnipotentQuotientCongr_mk]
  refine congrArg _ (Units.ext (Matrix.ext fun i j => ?_))
  rw [reindex_finCongr_apply, reindex_finCongr_apply]
  obtain ⟨s, hs⟩ := (rankOneExtensionCellCoordinates t).surjective (Fin.cast hc.symm i)
  obtain ⟨s', hs'⟩ := (rankOneExtensionCellCoordinates t).surjective (Fin.cast hc.symm j)
  have hpair (s : Fin (t + 1) ⊕ Fin 1) (i : Fin (1 + t + 1))
      (hs : rankOneExtensionCellCoordinates t s = Fin.cast hc.symm i) :
      Fin.cast (by omega : 1 + t + 1 = t + 1 + 1) i = finSumFinEquiv s := by
    apply Fin.ext
    rw [Fin.val_cast, ← Fin.val_cast hc.symm i, ← hs]
    rfl
  rw [← hs, ← hs', rankOneExtensionLowerBlock_apply, hpair s i hs, hpair s' j hs']
  change Matrix.fromBlocks g.val 0 x h.val.val
      (finSumFinEquiv.symm (finSumFinEquiv s)) (finSumFinEquiv.symm (finSumFinEquiv s')) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases s with s | s <;> rcases s' with s' | s'
  · rfl
  · rfl
  · rw [Subsingleton.elim s 0]
    rfl
  · rw [Subsingleton.elim s 0, Subsingleton.elim s' 0]
    rfl

end Chart

section Disintegration

private theorem quotientMeasureRankCast_symm {F : Type uF} [Field F]
    [TopologicalSpace F] {m n : ℕ} (h : m = n)
    (μ : @Measure (LeftQuotient (upperUnipotent m F))
      (borel (LeftQuotient (upperUnipotent m F)))) :
    quotientMeasureRankCast h.symm (quotientMeasureRankCast h μ) = μ := by
  subst n
  rfl

private theorem unipotentHaar_rightInvariant_of_index_eq
    {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F]
    [IsNonarchimedeanLocalField F] {m n : ℕ} (h : m = n) :
    letI := borel (upperUnipotent (m + 1) F)
    letI : BorelSpace (upperUnipotent (m + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F)
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    Measure.IsMulRightInvariant (unipotentHaar F m) →
      Measure.IsMulRightInvariant (unipotentHaar F n) := by
  subst n
  exact id

/-- `LowerBlockQuotientDisintegrationStatement` at `n = t`, `k = 0`, with the target rank
`t + 1 + 0 + 1` moved to `(1 + t) + 1`. The compatible measures, the additive Haar input
and the positive scalar are those of the statement. -/
theorem rankOneExtensionDisintegration_of_statement
    (hdis : LowerBlockQuotientDisintegrationStatement.{uF})
    (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (t : ℕ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (t + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (t + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient t F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent ((1 + t) + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent ((1 + t) + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient (1 + t) F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient (1 + t) F.Carrier) := ⟨rfl⟩
    letI := borel (lowerTriangularSubgroup 1 F.Carrier)
    letI : BorelSpace (lowerTriangularSubgroup 1 F.Carrier) := ⟨rfl⟩
    ∀ (η : AdditiveHaarMeasure F.Carrier)
      [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
      [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (1 + t))]
      (μbase : Measure (LeftUnipotentQuotient t F.Carrier))
      (μind : Measure (LeftUnipotentQuotient (1 + t) F.Carrier)),
      IsCompatible (upperUnipotent (t + 1) F.Carrier)
        (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μbase →
      IsCompatible (upperUnipotent ((1 + t) + 1) F.Carrier)
        (generalLinearHaar F.Carrier (1 + t)) (unipotentHaar F.Carrier (1 + t)) μind →
      ∃ ρ : Measure (lowerTriangularSubgroup 1 F.Carrier),
        ρ.Regular ∧ SigmaFinite ρ ∧ ρ.IsOpenPosMeasure ∧
        IsFiniteMeasureOnCompacts ρ ∧ ρ.IsMulRightInvariant ∧
        ∃ C : ℝ, 0 < C ∧
          ∀ f : LeftUnipotentQuotient (1 + t) F.Carrier → ℂ, Measurable f →
            (Integrable f μind ↔
              Integrable (f ∘ rankOneExtensionQuotientChart)
                ((μbase.withDensity
                  (lowerBlockQuotientDensity F.canonicalTopologicalData (t + 1) 1)).prod
                    ((rectangularMeasure η 1 (t + 1)).prod ρ))) ∧
            (Integrable f μind →
              ∫ q, f q ∂μind =
                (C : ℂ) * ∫ z, f (rankOneExtensionQuotientChart z)
                  ∂(μbase.withDensity
                    (lowerBlockQuotientDensity F.canonicalTopologicalData (t + 1) 1)).prod
                      ((rectangularMeasure η 1 (t + 1)).prod ρ)) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (t + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (t + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient t F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent ((1 + t) + 1) F.Carrier)
  let : BorelSpace (upperUnipotent ((1 + t) + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient (1 + t) F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient (1 + t) F.Carrier) := ⟨rfl⟩
  let := borel (lowerTriangularSubgroup 1 F.Carrier)
  let : BorelSpace (lowerTriangularSubgroup 1 F.Carrier) := ⟨rfl⟩
  intro η hrightBase hrightInd μbase μind hbase hind
  have hi : t + 1 + 0 = 1 + t := by omega
  let := borel (Langlands.GeneralLinear (t + 1 + 0 + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (t + 1 + 0 + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (t + 1 + 0 + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (t + 1 + 0 + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient (t + 1 + 0) F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient (t + 1 + 0) F.Carrier) := ⟨rfl⟩
  let : Measure.IsMulRightInvariant (unipotentHaar F.Carrier (t + 1 + 0)) :=
    unipotentHaar_rightInvariant_of_index_eq hi.symm hrightInd
  let μraw := quotientMeasureRankCast (congrArg (· + 1) hi.symm) μind
  have hraw : IsCompatible (upperUnipotent (t + 1 + 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (t + 1 + 0))
      (unipotentHaar F.Carrier (t + 1 + 0)) μraw :=
    (compatible_quotientMeasureRankCast_iff hi.symm μind).2 hind
  rcases hdis p F t 0 η μbase μraw hbase hraw with
    ⟨_, _, _, _, ρ, hreg, hσ, hpos, hfc, hright, _, C, hC, _, htransfer⟩
  refine ⟨ρ, hreg, hσ, hpos, hfc, hright, C, hC, fun f hf => ?_⟩
  let hr := congrArg (· + 1) hi
  let fraw := f ∘ upperUnipotentQuotientCongr hr
  have hfraw : Measurable fraw :=
    (measurable_comp_upperUnipotentQuotientCongr hr f).2 hf
  obtain ⟨hiff, hint⟩ := htransfer fraw hfraw
  have hμ : quotientMeasureRankCast hr μraw = μind :=
    quotientMeasureRankCast_symm (congrArg (· + 1) hi.symm) μind
  have hifull : Integrable f μind ↔ Integrable fraw μraw := by
    simpa only [hμ] using integrable_quotientMeasureRankCast_iff hr μraw f
  have hifullIntegral : ∫ q, f q ∂μind = ∫ q, fraw q ∂μraw := by
    simpa only [hμ, fraw, Function.comp_def] using
      integral_quotientMeasureRankCast hr μraw f
  exact ⟨hifull.trans hiff, fun hfi => hifullIntegral.trans (hint (hifull.mp hfi))⟩

end Disintegration

end Langlands.RankinSelberg
