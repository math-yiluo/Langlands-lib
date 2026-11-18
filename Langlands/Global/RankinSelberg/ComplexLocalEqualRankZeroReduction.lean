import Langlands.Global.RankinSelberg.ComplexRankZeroLocal
import Langlands.Global.RankinSelberg.ComplexRankZeroWhittaker

/-! # The rank-one case of the complex equal-rank local functional equation

`ComplexLocalEqualFunctionalEquationStatement` is split by the rank index `r` into the
propositions `ComplexLocalEqualAtRankStatement r`. The case `r = 0` (`GL₁(ℂ) × GL₁(ℂ)`)
follows from the complex Tate statement `ComplexArchimedeanTateStatement`. Hence, given the
complex Tate statement, the equal-rank local statement at all positive ranks implies the full
equal-rank local statement. See the paired Markdown.
-/

noncomputable section

open MeasureTheory
open Langlands.LocalFactor.Archimedean

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

/-- `ComplexLocalEqualFunctionalEquationStatement` at the single rank index `r` (the group
`GL_(r+1)(ℂ)`): the same quantifiers, hypotheses and conclusions, with `r` fixed. -/
def ComplexLocalEqualAtRankStatement (r : ℕ) : Prop := by
  classical
  exact
  ∀ (d d' : List ComplexCharacterData), d.length = r + 1 → d'.length = r + 1 →
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData r) (W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ),
    W ∈ complexWhittakerModel r d a → W' ∈ complexWhittakerModel r d' (-a) →
  ∃ (σ : ℝ) (M Md : ℂ → ℂ),
    (∀ s : ℂ, σ < s.re → Integrable (complexEqualIntegrand W W' Φ s) D.measure) ∧
    (∀ s : ℂ, σ < s.re →
      Integrable (complexEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
        (ArchimedeanLocal.dualFunction (r + 1) W') (complexFourierTransform a Φ) s)
        D.measure) ∧
    DifferentiableOn ℂ (complexEqualIntegral D W W' Φ) {s : ℂ | σ < s.re} ∧
    DifferentiableOn ℂ (complexEqualDualIntegral a D W W' Φ) {s : ℂ | σ < s.re} ∧
    MeromorphicOn M Set.univ ∧ MeromorphicOn Md Set.univ ∧
    (∀ s : ℂ, σ < s.re → complexEqualIntegral D W W' Φ s = M s) ∧
    (∀ s : ℂ, σ < s.re → complexEqualDualIntegral a D W W' Φ s = Md s) ∧
    ∀ᶠ s in Filter.codiscrete ℂ,
      ((complexPairLFactor d d').denominator s)⁻¹ * Md (1 - s) =
        complexCentralSign d' ^ r *
          (complexPairEpsilon d d' a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) *
          ((complexPairLFactor (d.map ComplexCharacterData.inv)
            (d'.map ComplexCharacterData.inv)).denominator (1 - s))⁻¹ * M s

/-- The complex equal-rank local statement is the conjunction of its instances at every
rank. -/
theorem complexLocalEqualFunctionalEquationStatement_iff :
    ComplexLocalEqualFunctionalEquationStatement ↔ ∀ r : ℕ, ComplexLocalEqualAtRankStatement r :=
  ⟨fun h r => h r, fun h r => h r⟩

/-- **The `GL₁(ℂ) × GL₁(ℂ)` case.** The complex Tate statement implies the complex
equal-rank local statement at rank index `0`. -/
theorem complexLocalEqualAtRankStatement_zero
    (hTate : Langlands.LocalFactor.ComplexArchimedeanTateStatement) :
    ComplexLocalEqualAtRankStatement 0 := by
  intro d d' hd hd' a D W W' Φ hW hW'
  obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hd
  obtain ⟨c', rfl⟩ := List.length_eq_one_iff.mp hd'
  obtain ⟨C, hC⟩ := ComplexRankZero.exists_eq_of_mem_complexWhittakerModel hW
  obtain ⟨C', hC'⟩ := ComplexRankZero.exists_eq_of_mem_complexWhittakerModel hW'
  exact ComplexRankZero.complexEqual_rankZero hTate a c c' D hC hC' Φ

/-- **Rank-one reduction of the complex equal-rank local functional equation.** Given the
complex Tate statement, the complex equal-rank local statement at every positive rank index
implies the full `ComplexLocalEqualFunctionalEquationStatement`. -/
def ComplexLocalEqualRankZeroReductionStatement : Prop :=
  Langlands.LocalFactor.ComplexArchimedeanTateStatement →
    (∀ r : ℕ, 0 < r → ComplexLocalEqualAtRankStatement r) →
      ComplexLocalEqualFunctionalEquationStatement

/-- Proof of `ComplexLocalEqualRankZeroReductionStatement`: rank index `0` comes from
`complexLocalEqualAtRankStatement_zero`, the positive ranks from the hypothesis. -/
theorem complexLocalEqualRankZeroReductionStatement :
    ComplexLocalEqualRankZeroReductionStatement := by
  intro hTate hpos
  refine complexLocalEqualFunctionalEquationStatement_iff.mpr fun r => ?_
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact complexLocalEqualAtRankStatement_zero hTate
  · exact hpos r hr

end Langlands.Global.RankinSelbergGlobal
