import Langlands.Global.RankinSelberg.ComplexEqualNormalizedCharacterChange
import Langlands.Global.RankinSelberg.ComplexJacquetMultiplicityOne
import Langlands.Global.RankinSelberg.ComplexLocalEqualCanonicalContinuation

/-! # Exact normalized equal-rank inputs from canonical Jacquet values -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal (ComplexQuotientMeasureData complexSelfDualMeasure complexEqualIntegrand
  complexFourierTransform)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexCompactProfileFamily (characterList)
open ComplexJacquetContinuation (HasCanonicalEqualNormalization canonicalJacquetLine
  inducingLine_zero continuedJacquet complexLocalEqualCanonicalFamily)
open ComplexJacquetMultiplicityOne (exists_characterList complexJacquetMultiplicityOne)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

/-- Both equal-rank kernels are absolutely integrable in a common right half-plane
for each pair in the exact induced Whittaker models. -/
theorem complexLocalEqualPairConvergence {r : ℕ} {a : ℂˣ} {ds es : List ComplexCharacterData}
    (hd : ds.length = r + 1) (he : es.length = r + 1) (D : ComplexQuotientMeasureData r)
    (W V : Langlands.GeneralLinear (r + 1) ℂ → ℂ) (Φ : 𝓢(Fin (r + 1) → ℂ, ℂ))
    (hW : W ∈ complexWhittakerModel r ds a) (hV : V ∈ complexWhittakerModel r es (-a)) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (complexEqualIntegrand W V Φ s) D.measure ∧
      Integrable (complexEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
        (ArchimedeanLocal.dualFunction (r + 1) V)
        (complexFourierTransform a Φ) s) D.measure := by
  obtain ⟨l, p, rfl⟩ := exists_characterList ds hd
  obtain ⟨k, q, rfl⟩ := exists_characterList es he
  let μ := complexSelfDualMeasure a
  have hRange : complexWhittakerModel r (characterList l p) a =
      LinearMap.range (continuedJacquet μ (-a) l p) := by
    simpa only [neg_neg] using (complexJacquetMultiplicityOne r μ (-a) l p).2
  rw [hRange] at hW
  rw [(complexJacquetMultiplicityOne r μ a k q).2] at hV
  obtain ⟨f, rfl⟩ := hW
  obtain ⟨v, rfl⟩ := hV
  obtain ⟨σ, hI, _, _⟩ := complexLocalEqualCanonicalFamily μ a D l k p p q q f v Φ 1
  refine ⟨σ, fun s hs => ?_⟩
  have hz : (0 : ℂ) ∈ Metric.ball 0 1 := Metric.mem_ball_self zero_lt_one
  simpa only [canonicalJacquetLine, inducingLine_zero, continuedJacquet, LinearMap.comp_apply,
    LinearMap.proj_apply] using hI 0 hz s hs

/-- At a fixed rank, the entire-normalized equation for canonical Jacquet vectors
and the standard trace character gives the full normalized equal-rank induction input. -/
def ComplexEqualNormalizedFromCanonicalStatement : Prop :=
  ∀ (r : ℕ),
    (∀ (D : ComplexQuotientMeasureData r) (l k : Fin (r + 1) → ℤ)
      (p q : Fin (r + 1) → ℂ) (Φ : 𝓢(Fin (r + 1) → ℂ, ℂ)),
      HasCanonicalEqualNormalization (complexSelfDualMeasure 1) 1 D l k p q Φ) →
    ComplexLocalEqualNormalizedAtRankStatement r

theorem complexEqualNormalizedFromCanonical : ComplexEqualNormalizedFromCanonicalStatement := by
  intro r h
  apply complexEqualNormalizedCharacterChange r
  intro ds es hd he D W V Φ hW hV
  have hConv := complexLocalEqualPairConvergence hd he D W V Φ hW hV
  obtain ⟨l, p, rfl⟩ := exists_characterList ds hd
  obtain ⟨k, q, rfl⟩ := exists_characterList es he
  let μ := complexSelfDualMeasure 1
  have hRange : complexWhittakerModel r (characterList l p) 1 =
      LinearMap.range (continuedJacquet μ (-1) l p) := by
    simpa only [neg_neg] using (complexJacquetMultiplicityOne r μ (-1) l p).2
  rw [hRange] at hW
  rw [(complexJacquetMultiplicityOne r μ 1 k q).2] at hV
  obtain ⟨f, rfl⟩ := hW
  obtain ⟨v, rfl⟩ := hV
  exact ⟨hConv, h D l k p q Φ f v⟩

end Langlands.Global.RankinSelbergGlobal
