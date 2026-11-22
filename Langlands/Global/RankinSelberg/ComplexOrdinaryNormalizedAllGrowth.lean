import Langlands.Global.Factors.CuspidalPairPoleFromLocalTests
import Langlands.Global.RankinSelberg.ComplexPlaceUnequalFunctionalEquationProof
import Langlands.Global.RankinSelberg.OrdinaryNormalizationUniqueness

/-! # Entire complex ordinary normalizations and their strip growth -/

noncomputable section

open scoped NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.LocalFactor.Archimedean
open ArchimedeanLocal
open ComplexJacquet (HasComplexPairNormalizedGrowth)
open CuspidalPairPoles (ComplexOrdinaryNormalizedStripGrowthStatement)
open FunctionalEquationComparison.CompletedEquationAdapter (complexPairLFactor_denominator_ne_zero)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

private theorem ordinaryNormalization_of_growth {ds es : List ComplexCharacterData}
    {a : ℂˣ} {c : ℂ} {I Id : ℂ → ℂ} (h : HasComplexPairNormalizedGrowth ds es a c I Id) :
    ∃ N : OrdinaryIntegralNormalization I (fun s => ((complexPairLFactor ds es).denominator s)⁻¹),
      HasStripExponentialGrowth N.value := by
  obtain ⟨N, _, hN, _, hNg, _, ⟨τ, hτ⟩, _⟩ := h
  obtain ⟨σ, hσ⟩ := complexPairLFactor_denominator_ne_zero ds es
  refine ⟨⟨N, fun s _ => hN.analyticAt s, ⟨max τ σ, fun s hs => ?_⟩⟩, hNg⟩
  rw [(hτ s ((le_max_left _ _).trans_lt hs)).1,
    mul_comm ((complexPairLFactor ds es).denominator s) (I s), mul_assoc,
    mul_inv_cancel₀ (hσ s ((le_max_right _ _).trans_lt hs)), mul_one]

/-- Every ordinary complex pair integral has an entire normalization in all ranks,
and every such normalization has exponential growth at most on a vertical strip. -/
def ComplexOrdinaryNormalizedAllGrowthStatement : Prop :=
  ComplexOrdinaryNormalizedContinuationStatement ∧ ComplexOrdinaryNormalizedStripGrowthStatement

theorem complexOrdinaryNormalizedAllGrowth : ComplexOrdinaryNormalizedAllGrowthStatement := by
  have hUnequal (r t : ℕ) (h : t < r) (ds es : List ComplexCharacterData)
      (hd : ds.length = r + 1) (he : es.length = t + 1) (a : ℂˣ) (D : ComplexQuotientMeasureData t) :
      HasEntireOrdinaryNormalizations (complexOrdinaryUnequalTest h ds es a D) (complexPairLFactor ds es) ∧
      HasOrdinaryNormalizationStripGrowth (complexOrdinaryUnequalTest h ds es a D) (complexPairLFactor ds es) := by
    refine ordinaryNormalizationGrowthFromExistence _ _ (complexPairLFactor_denominator_ne_zero ds es) ?_
    rintro ⟨W, V⟩
    exact ordinaryNormalization_of_growth (complexUnequalNormalizedGrowth r t h ds es hd he a D W V W.2 V.2)
  have hEqual (r : ℕ) (ds es : List ComplexCharacterData)
      (hd : ds.length = r + 1) (he : es.length = r + 1) (a : ℂˣ) (D : ComplexQuotientMeasureData r) :
      HasEntireOrdinaryNormalizations (complexOrdinaryEqualTest r ds es a D) (complexPairLFactor ds es) ∧
      HasOrdinaryNormalizationStripGrowth (complexOrdinaryEqualTest r ds es a D) (complexPairLFactor ds es) := by
    refine ordinaryNormalizationGrowthFromExistence _ _ (complexPairLFactor_denominator_ne_zero ds es) ?_
    rintro ⟨W, V, Φ⟩
    exact ordinaryNormalization_of_growth (complexEqualGrowth_scaled r (standardEqualGrowth r)
      ds es hd he a D W V Φ W.2 V.2)
  exact ⟨⟨fun r t h ds es hd he a D => (hUnequal r t h ds es hd he a D).1,
    fun r ds es hd he a D => (hEqual r ds es hd he a D).1⟩,
    ⟨fun r t h ds es hd he a => (hUnequal r t h ds es hd he a (complexQuotientMeasureData t)).2,
    fun r ds es hd he a => (hEqual r ds es hd he a (complexQuotientMeasureData r)).2⟩⟩

end Langlands.Global.RankinSelbergGlobal
