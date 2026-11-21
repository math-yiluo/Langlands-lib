import Langlands.Global.RankinSelberg.ComplexGodementFiniteNonzero
import Langlands.Global.RankinSelberg.ComplexJacquetRegularity

/-! # Nonzero canonical complex Jacquet evaluation at every inducing parameter -/

noncomputable section
open MeasureTheory
open scoped Classical Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

open Langlands.Archimedean (characterOfParams)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open ComplexCompactProfileFamily (characterList compactRestriction compactRestriction_isCompactProfile)
open ComplexGodement (SmallerProfile smallerWeights smallerExponents addedCharacter smallerSection
  godementSection exists_finite_test_continuedValue_ne_zero)
open ComplexGodementGeneratorFamily (generatorFamily)
open ComplexRankZero (characterFunction characterFunction_mem characterFunction_one)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel

/-- In each positive rank and at every inducing parameter a compact-finite standard vector
has nonzero canonical Jacquet value at the identity. -/
def ComplexJacquetNonzeroStatement : Prop :=
  ∀ (r : ℕ) (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : Fin (r + 1) → ℤ) (p : Fin (r + 1) → ℂ),
    ∃ f : Automorphic.complexStandardKFinite (r + 1) (characterList l p),
      continuedJacquet μ a l p f 1 ≠ 0

set_option maxHeartbeats 1000000 in
theorem complexJacquetNonzero : ComplexJacquetNonzeroStatement := by
  intro r μ a
  induction r with
  | zero =>
    intro l p
    let d := characterOfParams (l 0) (p 0)
    have hlist : characterList l p = [d] := by simp only [characterList, List.ofFn_succ, List.ofFn_zero, d]
    let f : Automorphic.complexStandardKFinite (0 + 1) (characterList l p) :=
      ⟨characterFunction d, hlist.symm ▸ characterFunction_mem d⟩
    refine ⟨f, ?_⟩
    rw [continuedJacquet_rankOne]
    change characterFunction d 1 ≠ 0
    rw [characterFunction_one]
    exact one_ne_zero
  | succ r ih =>
    intro l p
    obtain ⟨f₀, hf₀⟩ := ih (smallerWeights l) (smallerExponents p)
    let f : SmallerProfile l := ⟨compactRestriction f₀.val, compactRestriction_isCompactProfile f₀.2⟩
    let W := canonicalJacquetFamily μ a (smallerWeights l) f.val f.2
    let ν := complexGeneralLinearHaar (r + 1)
    have hW := canonicalJacquetFamily_properties μ a (smallerWeights l) f.val f.2
    obtain ⟨δ, hδ, hB⟩ := hW.2.2.1 (smallerExponents p)
    have hWne : W (smallerExponents p) 1 ≠ 0 := hf₀
    obtain ⟨Φ, hΦ, hfull, hfinite, hne⟩ := exists_finite_test_continuedValue_ne_zero ν μ a
      (characterOfParams (l 0) 0) (Metric.ball (smallerExponents p) δ) W (fun q _ => hW.1 q) hB
      (smallerExponents p) (Metric.mem_ball_self hδ) hWne (p 0)
    let F : Automorphic.complexStandardKFinite (r + 1 + 1) (characterList l p) :=
      ⟨godementSection ν (addedCharacter l p) Φ (smallerSection p f),
        godementSection_mem_standardKFinite ν l Φ hΦ hfull hfinite f p⟩
    have he : continuedJacquet μ a l p F = generatorFamily ν μ a l Φ W p :=
      complexJacquetGeneratorEvaluation ν μ a l Φ hΦ hfull hfinite f p
    refine ⟨F, ?_⟩
    rw [he]
    exact hne

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation
