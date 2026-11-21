import Langlands.Global.RankinSelberg.ComplexGapCanonicalSpan
import Langlands.Global.RankinSelberg.ComplexAdjacentCanonical
import Langlands.Global.RankinSelberg.ComplexJacquetMultiplicityOne
import Langlands.Global.RankinSelberg.ComplexLocalDualConvergence
import Langlands.Global.RankinSelberg.ComplexLocalUnequalFromNormalized

/-! # From the normalized monomial comparison to the exact unequal pair -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapCanonicalGrowth

open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ArchimedeanLocal (ComplexQuotientMeasureData complexSelfDualMeasure complexUnequalIntegral
  complexUnequalDualIntegral)
open ComplexAdjacentUnfolding (complexUnequalCanonicalGrowthFromChamber complexUnequalNormalizedGrowthSpace
  complexUnequalNormalizedGrowthSpan)
open ComplexCompactProfileFamily (characterList)
open ComplexGapCanonicalSpan (rotatedGaussianValues complexGapCanonicalSpan)
open ComplexGapExactRestriction (rotatedValue)
open ComplexGapRankCoordinates (rankLT)
open ComplexGodement (characterList_cons)
open ComplexGodementGaussianPolynomial (Coordinates gaussianPolynomial)
open ComplexJacquet (HasComplexPairNormalizedGrowth)
open ComplexJacquetContinuation (continuedJacquet complexJacquetIntertwiner HasUnequalCanonicalPairGrowth)
open ComplexJacquetMultiplicityOne (complexJacquetMultiplicityOne exists_characterList)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℂ

/-- The normalized local pair with exponential strip growth, in the integrating-character convention. -/
def ComplexLocalUnequalGrowthAtRanks (r t : ℕ) (h : t < r) : Prop :=
  ∀ (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = t + 1 →
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData t) (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ),
    W ∈ complexWhittakerModel r ds (-a) → V ∈ complexWhittakerModel t es a →
    HasComplexPairNormalizedGrowth ds es (-a) (complexCentralSign es ^ r)
      (complexUnequalIntegral h D W V) (complexUnequalDualIntegral h (-a) D W V)

variable (t q : ℕ)
local notation "k" => t + 1
local notation "n" => t + 1 + q + 1
local notation "h" => rankLT t (q + 1)
local notation "H" => G (t + 1)

/-- The needed strip-growing reflection on each rotated split Gaussian monomial. -/
def ComplexGapMonomialGrowth : Prop :=
  ∀ (ds es : List ComplexCharacterData), ds.length = n → es.length = k →
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData t) (d : ComplexCharacterData)
      (U : complexWhittakerModel (t + 1 + q) ds (-a))
      (i : Coordinates n (n + 1) →₀ ℕ) (c : ℂ)
      (B : Automorphic.complexStandardKFinite k es →ₗ[ℂ] (H → ℂ)), IsComplexWhittakerIntertwiner t es a B →
  ∀ f : Automorphic.complexStandardKFinite k es,
    let W := rotatedValue t q a d (operatorToEntry (gaussianPolynomial (MvPolynomial.monomial i c))) U.val 0
    W ∈ complexWhittakerModel n (d :: ds) (-a) →
    HasComplexPairNormalizedGrowth (d :: ds) es (-a) (complexCentralSign es ^ n)
      (complexUnequalIntegral h D W (B f)) (complexUnequalDualIntegral h (-a) D W (B f))

/-- Spanning and chamber removal extend the monomial comparison to every exact model vector. -/
def ComplexGapCanonicalGrowthStatement : Prop :=
  ComplexGapMonomialGrowth t q → ComplexLocalUnequalGrowthAtRanks n t h

theorem complexGapCanonicalGrowth : ComplexGapCanonicalGrowthStatement t q := by
  intro hMono ds es hds hes a D W V hW hV
  obtain ⟨l, p, rfl⟩ := exists_characterList ds hds
  obtain ⟨w, b, rfl⟩ := exists_characterList es hes
  let μ := complexSelfDualMeasure a
  have hWrange := (complexJacquetMultiplicityOne n μ a l p).2
  rw [hWrange] at hW
  obtain ⟨F, rfl⟩ := hW
  let B := continuedJacquet μ (-a) w b
  have hB : IsComplexWhittakerIntertwiner t (characterList w b) a B := by
    simpa only [B, neg_neg] using complexJacquetIntertwiner t μ (-a) w b
  have hVrange : complexWhittakerModel t (characterList w b) a = LinearMap.range B := by
    simpa only [B, neg_neg] using (complexJacquetMultiplicityOne t μ (-a) w b).2
  obtain ⟨f, hf⟩ := hVrange ▸ hV
  have hStrong (z : Fin n → ℂ) : ∃ M : ℕ, ∀ (e : Fin (n + 1) → ℂ),
      ComplexGodement.smallerExponents e = z → e ∈ ComplexJacquetChamberHolomorphic.chamber n →
      ((n : ℕ) : ℝ) + M ≤ (e 0 + ((((n : ℕ) : ℂ) + 1) / 2)).re →
      HasUnequalCanonicalPairGrowth h μ a D l e (characterList w b) V := by
    obtain ⟨M, hSp⟩ := complexGapCanonicalSpan t q l z
    refine ⟨M, fun e he hc hd J => ?_⟩
    let S := complexUnequalNormalizedGrowthSpace h D (characterList l e) (characterList w b) (-a) V
    have hS : Submodule.span ℂ (rotatedGaussianValues t q l e a) ≤ S := by
      apply Submodule.span_le.mpr
      rintro W₀ ⟨hW₀, U, i, c, rfl⟩
      let d := ComplexGodement.addedCharacter l e
      let ds₀ := ComplexGodement.retainedCharacters l e
      let W₁ := rotatedValue t q a d (operatorToEntry (gaussianPolynomial (MvPolynomial.monomial i c))) U.val 0
      have hds₀ : ds₀.length = n := List.length_ofFn
      have hList : characterList l e = d :: ds₀ := characterList_cons l e
      refine (complexUnequalNormalizedGrowthSpan n t h D (characterList l e) (characterList w b) (-a) W₁ V).2 ⟨?_, ?_⟩
      · have hV' : V ∈ complexWhittakerModel t (characterList w b) (-(-a)) := by simpa only [neg_neg] using hV
        exact complexLocalUnequalConvergence h (characterList l e) (characterList w b) (-a) D ⟨W₁, hW₀⟩ ⟨V, hV'⟩
      · rw [hList, ← hf]
        exact hMono ds₀ (characterList w b) hds₀ List.length_ofFn a D d U i c B hB f (hList ▸ hW₀)
    have hJ := hS (hSp e he hc hd a J)
    exact ((complexUnequalNormalizedGrowthSpan n t h D (characterList l e) (characterList w b) (-a) _ V).1 hJ).2
  exact complexUnequalCanonicalGrowthFromChamber h μ a D l w b V hV hStrong p F

end Langlands.Global.RankinSelbergGlobal.ComplexGapCanonicalGrowth
