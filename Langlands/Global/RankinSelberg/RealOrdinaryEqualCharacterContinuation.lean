import Langlands.Global.RankinSelberg.RealLocalUniformPositiveEqualContinuationProof
import Langlands.Global.RankinSelberg.RealPrincipalSeriesQuotient
import Langlands.Global.RankinSelberg.RealWhittakerUniformGrowth
import Langlands.LocalFactor.RealPairLFactorNormalization

/-! # Equal-rank real ordinary continuation with weight-zero induced blocks -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal RealJacquet RealPrincipalSeries
open RealJacquetFrobenius (charData)

private theorem expand_eq_normalize_of_weight_zero (ds : List RealBlock)
    (h : ∀ d : ComplexCharacterData, RealBlock.induced d ∈ ds → d.weight = 0) :
    expand ds = ds.flatMap realBlockNormalize := by
  induction ds with
  | nil => rfl
  | cons b ds ih =>
    have hTail := ih (fun d hd => h d (List.mem_cons_of_mem b hd))
    cases b with
    | character c =>
      change RealBlock.character c :: expand ds = RealBlock.character c :: ds.flatMap realBlockNormalize
      rw [hTail]
    | induced d =>
      have hp := h d List.mem_cons_self
      change
        [RealBlock.character (charData (RealGammaReflection.positionParity d.weight.natAbs)
          (d.exponent + (d.weight.natAbs : ℂ) / 2)),
          RealBlock.character (charData 0 (d.exponent - (d.weight.natAbs : ℂ) / 2))] ++ expand ds =
        realBlockNormalize (.induced d) ++ ds.flatMap realBlockNormalize
      simp [hTail, hp, realBlockNormalize, realBlockExpand, RealBlock.positiveWeight,
        RealGammaReflection.positionParity]

namespace RealJacquet.HasRealPairNormalizedGrowth

/-- An entire normalized pair provides an ordinary normalization of its primal integral. -/
theorem ordinaryNormalization
    {ds es dds ees : List RealBlock} {b : ℝˣ} {c : NNReal} {hc : 0 < c}
    {sign : ℂ} {Z Zd : ℂ → ℂ}
    (h : HasRealPairNormalizedGrowth ds es dds ees b c hc sign Z Zd) :
    Nonempty (OrdinaryIntegralNormalization Z (fun s => ((realPairLFactor ds es).denominator s)⁻¹)) := by
  obtain ⟨N, _, hN, _, _, _, ⟨σ, hσ⟩, _⟩ := h
  obtain ⟨τ, hτ⟩ := ArchimedeanRealPairFactor.realLFactor_ne_zero (realPairBlocks ds es)
  refine ⟨⟨N, fun s _ => hN.analyticAt s, ⟨max σ τ, fun s hs => ?_⟩⟩⟩
  have hd : (realPairLFactor ds es).denominator s ≠ 0 := hτ s ((le_max_right _ _).trans_lt hs)
  rw [(hσ s ((le_max_left _ _).trans_lt hs)).1, mul_comm ((realPairLFactor ds es).denominator s),
    mul_assoc, mul_inv_cancel₀ hd, mul_one]

end RealJacquet.HasRealPairNormalizedGrowth

/-- Equal-rank exact ordinary continuation for arbitrary real characters and weight-zero
induced blocks, with the prescribed block factor. -/
def RealOrdinaryEqualCharacterContinuationStatement : Prop :=
  ∀ (r : ℕ) (ds es : List RealBlock), realRank ds = r + 1 → realRank es = r + 1 →
    (∀ d : ComplexCharacterData, RealBlock.induced d ∈ ds → d.weight = 0) →
    (∀ e : ComplexCharacterData, RealBlock.induced e ∈ es → e.weight = 0) →
    ∀ (a : ℝˣ) (D : RealQuotientMeasureData r),
      HasEntireOrdinaryNormalizations (realOrdinaryEqualTest r ds es a D) (realPairLFactor ds es)

theorem realOrdinaryEqualCharacterContinuation : RealOrdinaryEqualCharacterContinuationStatement := by
  rintro r ds es hd he hds hes a D ⟨W, V, Φ⟩
  have hFactors : realPairLFactor (ascendingExpand ds) (ascendingExpand es) = realPairLFactor ds es := by
    rw [realPairLFactor_perm (ascendingExpand_perm ds) (ascendingExpand_perm es),
      expand_eq_normalize_of_weight_zero ds hds, expand_eq_normalize_of_weight_zero es hes,
      realPairLFactor_normalize_left, realPairLFactor_normalize_right]
  have hG := realLocalEqualCharacterGrowth_of_canonicalPremises
    RealUniformCanonicalRange.realUniformCanonicalRangePremise
    RealUniformCanonicalRange.realCanonicalStandardEvaluationPremise r
  have hW : (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) ∈
      realUniformWhittakerModel r (ascendingExpand ds) a := by
    apply uniformModel_le_ascendingExpand r ds hd a
    rw [← realWhittakerModels_eq r ds hd a]
    exact W.2
  have hV : (V : Langlands.GeneralLinear (r + 1) ℝ → ℂ) ∈
      realUniformWhittakerModel r (ascendingExpand es) (-a) := by
    apply uniformModel_le_ascendingExpand r es he (-a)
    rw [← realWhittakerModels_eq r es he (-a)]
    exact V.2
  have hN := (hG (ascendingExpand ds) (ascendingExpand es) ⟨_, rfl⟩ ⟨_, rfl⟩
    ((realRank_ascendingExpand ds).trans hd) ((realRank_ascendingExpand es).trans he)
    a D W V Φ hW hV).ordinaryNormalization
  rwa [hFactors] at hN

end Langlands.Global.RankinSelbergGlobal
