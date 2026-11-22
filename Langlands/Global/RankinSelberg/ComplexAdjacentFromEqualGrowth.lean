import Langlands.Global.RankinSelberg.ComplexAdjacentFromEqual
import Langlands.Global.RankinSelberg.ComplexEqualNormalizedFromCanonical

/-! # Growth-preserving adjacent-rank induction at a fixed character -/

noncomputable section

open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal Langlands.LocalFactor.Archimedean
open ComplexAdjacentUnfolding (HasAdjacentLowerEqualGrowthInputs complexAdjacentCanonicalGrowth
  complexFourierTransform_splitRowTransform splitRowTransform)
open ComplexCompactProfileFamily (characterList)
open ComplexJacquet (HasComplexPairNormalizedGrowth)
open ComplexJacquetContinuation (continuedJacquet complexJacquetIntertwiner)
open ComplexJacquetMultiplicityOne (exists_characterList complexJacquetMultiplicityOne)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

/-- At a fixed trace character, the entire equal-rank normalization with strip growth
implies the adjacent-rank normalization with strip growth. -/
def ComplexAdjacentFromEqualGrowthAtCharacterStatement (r : ℕ) (a : ℂˣ) : Prop :=
  (∀ (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = r + 1 →
    ∀ (D : ComplexQuotientMeasureData r) (U V : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
      (φ : 𝓢(Fin (r + 1) → ℂ, ℂ)),
      U ∈ complexWhittakerModel r ds a → V ∈ complexWhittakerModel r es (-a) →
      HasComplexPairNormalizedGrowth ds es a (complexCentralSign es ^ r)
        (complexEqualIntegral D U V φ) (complexEqualDualIntegral a D U V φ)) →
  ∀ (ds es : List ComplexCharacterData), ds.length = r + 2 → es.length = r + 1 →
    ∀ (D : ComplexQuotientMeasureData r) (W : Langlands.GeneralLinear (r + 2) ℂ → ℂ)
      (V : Langlands.GeneralLinear (r + 1) ℂ → ℂ),
      W ∈ complexWhittakerModel (r + 1) ds a → V ∈ complexWhittakerModel r es (-a) →
      HasComplexPairNormalizedGrowth ds es a (complexCentralSign es ^ (r + 1))
        (complexUnequalIntegral (Nat.lt_succ_self r) D W V)
        (complexUnequalDualIntegral (Nat.lt_succ_self r) a D W V)

theorem complexAdjacentFromEqualGrowthAtCharacter (r : ℕ) (a : ℂˣ) :
    ComplexAdjacentFromEqualGrowthAtCharacterStatement r a := by
  intro hEqual ds es hd he D W V hW hV
  obtain ⟨l, p, rfl⟩ := exists_characterList ds hd
  obtain ⟨k, q, rfl⟩ := exists_characterList es he
  let μ := complexSelfDualMeasure (-a)
  have hL : complexWhittakerModel (r + 1) (characterList l p) a =
      LinearMap.range (continuedJacquet μ (-a) l p) := by
    simpa only [neg_neg] using (complexJacquetMultiplicityOne (r + 1) μ (-a) l p).2
  rw [hL] at hW
  rw [(complexJacquetMultiplicityOne r μ a k q).2] at hV
  obtain ⟨f, rfl⟩ := hW
  obtain ⟨v, rfl⟩ := hV
  have hLower (e : Fin (r + 1) → ℂ) :
      HasAdjacentLowerEqualGrowthInputs D (characterList (ComplexGodement.smallerWeights l) e)
        (characterList k q) (-a) := by
    intro U V hV φ
    let Φ := splitRowTransform (-a) φ
    have hU : U.val ∈ complexWhittakerModel r (characterList (ComplexGodement.smallerWeights l) e) a := by
      simpa only [neg_neg] using U.2
    have hF : complexFourierTransform a Φ = φ := by
      simpa only [Φ, neg_neg] using funext (complexFourierTransform_splitRowTransform (-a) φ)
    obtain ⟨σ, hσ⟩ := complexLocalEqualPairConvergence List.length_ofFn List.length_ofFn D U.val V Φ hU hV
    refine ⟨⟨σ, fun s hs => ⟨(hσ s hs).1, ?_⟩⟩, ?_⟩
    · simpa only [hF] using (hσ s hs).2
    · simpa only [Φ, neg_neg, characterList] using
        hEqual _ _ List.length_ofFn List.length_ofFn D U.val V Φ hU hV
  have h := complexAdjacentCanonicalGrowth D l k q (-a) hLower (continuedJacquet μ a k q)
    (complexJacquetIntertwiner r μ a k q) v p f
  simpa only [neg_neg] using h

/-- The adjacent step at the standard trace character. -/
def ComplexAdjacentFromEqualGrowthStatement : Prop :=
  ∀ (r : ℕ),
    (∀ (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = r + 1 →
      ∀ (D : ComplexQuotientMeasureData r) (U V : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
        (φ : 𝓢(Fin (r + 1) → ℂ, ℂ)),
        U ∈ complexWhittakerModel r ds 1 → V ∈ complexWhittakerModel r es (-1) →
        HasComplexPairNormalizedGrowth ds es 1 (complexCentralSign es ^ r)
          (complexEqualIntegral D U V φ) (complexEqualDualIntegral 1 D U V φ)) →
    ∀ (ds es : List ComplexCharacterData), ds.length = r + 2 → es.length = r + 1 →
      ∀ (D : ComplexQuotientMeasureData r) (W : Langlands.GeneralLinear (r + 2) ℂ → ℂ)
        (V : Langlands.GeneralLinear (r + 1) ℂ → ℂ),
        W ∈ complexWhittakerModel (r + 1) ds 1 → V ∈ complexWhittakerModel r es (-1) →
        HasComplexPairNormalizedGrowth ds es 1 (complexCentralSign es ^ (r + 1))
          (complexUnequalIntegral (Nat.lt_succ_self r) D W V)
          (complexUnequalDualIntegral (Nat.lt_succ_self r) 1 D W V)

theorem complexAdjacentFromEqualGrowth : ComplexAdjacentFromEqualGrowthStatement :=
  fun r => complexAdjacentFromEqualGrowthAtCharacter r 1

end Langlands.Global.RankinSelbergGlobal
