import Langlands.Representation.Aubert.General.RationalWeylComparisonTarget
import Langlands.GroupScheme.Rational.NormalizerPointsInfiniteFieldProof

/-! # Scheme and point-image Weyl comparisons over local fields -/

noncomputable section

universe u

namespace Langlands.Aubert.General.RationalPointFamily

/-- The actual normalizer and full-centralizer comparisons follow from
rational-point detection for split tori over infinite fields. -/
theorem rationalWeylComparison :
    RationalWeylComparisonStatement.{u} := by
  intro k _ _ _ _ G hG T i hi
  obtain ⟨x, hx⟩ := Valuation.IsNontrivial.exists_one_lt
    (v := ValuativeRel.valuation k)
  have : Infinite k := by
    refine Infinite.of_injective (fun n : ℕ => x ^ n) ?_
    intro m n hmn
    apply (pow_right_strictMono₀ hx).injective
    simpa only [map_pow] using congrArg (ValuativeRel.valuation k) hmn
  exact GroupScheme.normalizerPointsInfiniteField k G hG T i hi.isSplitSubtorus

end Langlands.Aubert.General.RationalPointFamily
