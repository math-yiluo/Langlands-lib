import Langlands.Global.RankinSelberg.ComplexAdjacentCanonical
import Langlands.Global.RankinSelberg.ComplexEqualNormalizedRankZero
import Langlands.Global.RankinSelberg.ComplexJacquetMultiplicityOne

/-! # The adjacent-rank step from the normalized equal-rank equation -/

noncomputable section

open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal Langlands.LocalFactor.Archimedean
open ComplexAdjacentUnfolding (HasComplexPairNormalization HasAdjacentLowerEqualInputs
  splitRowTransform complexFourierTransform_splitRowTransform complexAdjacentCanonical)
open ComplexCompactProfileFamily (characterList)
open ComplexJacquetMultiplicityOne (exists_characterList complexJacquetMultiplicityOne)
open ComplexJacquetContinuation (continuedJacquet complexJacquetIntertwiner)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

/-- The entire normalized unequal-rank equation for a prescribed pair of ranks. -/
def ComplexLocalUnequalNormalizedAtRanksStatement (r t : ℕ) (h : t < r) : Prop :=
  ∀ (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = t + 1 →
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData t)
    (W : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (V : Langlands.GeneralLinear (t + 1) ℂ → ℂ),
    W ∈ complexWhittakerModel r ds a → V ∈ complexWhittakerModel t es (-a) →
    HasComplexPairNormalization ds es a (complexCentralSign es ^ r)
      (complexUnequalIntegral h D W V) (complexUnequalDualIntegral h a D W V)

/-- Specializing the equal-rank equation to the partial row Fourier test gives
the two convergence inputs and the normalization used by the adjacent calculation. -/
theorem hasAdjacentLowerEqualInputs_of_equalNormalized {r : ℕ}
    (h : ComplexLocalEqualNormalizedAtRankStatement r)
    (D : ComplexQuotientMeasureData r) (ds es : List ComplexCharacterData)
    (hd : ds.length = r + 1) (he : es.length = r + 1) (a : ℂˣ) :
    HasAdjacentLowerEqualInputs D ds es a := by
  intro U V hV φ
  have hV' : V ∈ complexWhittakerModel r es (-(-a)) := by simpa only [neg_neg] using hV
  obtain ⟨⟨σ, hσ⟩, hN⟩ := h (-a) ds es hd he D U.val V (splitRowTransform a φ) U.2 hV'
  refine ⟨⟨σ, fun s hs => ⟨(hσ s hs).1, ?_⟩⟩, hN⟩
  have hF : complexFourierTransform (-a) (splitRowTransform a φ) = φ :=
    funext (complexFourierTransform_splitRowTransform a φ)
  rw [← hF]
  exact (hσ s hs).2

/-- The normalized equal-rank equation at one rank implies the full normalized
adjacent-rank equation with that smaller rank. -/
def ComplexAdjacentFromEqualStatement : Prop :=
  ∀ r : ℕ, ComplexLocalEqualNormalizedAtRankStatement r →
    ComplexLocalUnequalNormalizedAtRanksStatement (r + 1) r (Nat.lt_succ_self r)

theorem complexAdjacentFromEqual : ComplexAdjacentFromEqualStatement := by
  intro r hEqual ds es hd he a D W V hW hV
  obtain ⟨l, p, rfl⟩ := exists_characterList ds hd
  obtain ⟨k, q, rfl⟩ := exists_characterList es he
  let μ := complexSelfDualMeasure (-a)
  have hLarge : complexWhittakerModel (r + 1) (characterList l p) a =
      LinearMap.range (continuedJacquet μ (-a) l p) := by
    simpa only [neg_neg] using (complexJacquetMultiplicityOne (r + 1) μ (-a) l p).2
  have hSmall : complexWhittakerModel r (characterList k q) (-a) =
      LinearMap.range (continuedJacquet μ a k q) :=
    (complexJacquetMultiplicityOne r μ a k q).2
  rw [hLarge] at hW
  rw [hSmall] at hV
  obtain ⟨f, rfl⟩ := hW
  obtain ⟨v, rfl⟩ := hV
  have h := complexAdjacentCanonical D l k q (-a)
    (fun e => hasAdjacentLowerEqualInputs_of_equalNormalized hEqual D _ _
      List.length_ofFn List.length_ofFn (-a)) (continuedJacquet μ a k q)
    (complexJacquetIntertwiner r μ a k q) v p f
  simpa only [neg_neg] using h

/-- The normalized local functional equation for `GL₂(ℂ) × GL₁(ℂ)`. -/
theorem complexUnequalNormalizedRankTwoRankOne :
    ComplexLocalUnequalNormalizedAtRanksStatement 1 0 Nat.zero_lt_one :=
  complexAdjacentFromEqual 0 complexEqualNormalizedRankZero

end Langlands.Global.RankinSelbergGlobal
