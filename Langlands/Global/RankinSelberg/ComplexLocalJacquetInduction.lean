import Langlands.Global.RankinSelberg.ComplexLocalAdjacentJacquetExpansion
import Langlands.Global.RankinSelberg.ComplexLocalEqualRankZero

/-! # Simultaneous equal-rank and adjacent-rank induction for complex Jacquet integrals -/

noncomputable section

open MeasureTheory
open Langlands.LocalFactor.Archimedean

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

/-- The absolute convergence and matched expansion needed for the adjacent-rank step. -/
def ComplexLocalAdjacentJacquetDataStatement : Prop :=
  ∀ (r : ℕ) (d : ComplexCharacterData) (ds es : List ComplexCharacterData),
    ds.length = r + 1 → es.length = r + 1 →
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (W : Langlands.GeneralLinear (r + 2) ℂ → ℂ)
    (V : Langlands.GeneralLinear (r + 1) ℂ → ℂ),
    W ∈ complexWhittakerModel (r + 1) (d :: ds) a → V ∈ complexWhittakerModel r es (-a) →
    HasAdjacentJacquetExpansion d ds es a D W V ∧ HasAdjacentJacquetConvergence a D W V

/-- The absolute convergence and matched expansion needed for the equal-rank successor step. -/
def ComplexLocalEqualJacquetDataStatement : Prop :=
  ∀ (r : ℕ) (d : ComplexCharacterData) (ds es : List ComplexCharacterData),
    ds.length = r + 1 → es.length = r + 2 →
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData (r + 1))
    (W V : Langlands.GeneralLinear (r + 2) ℂ → ℂ)
    (Φ : SchwartzMap (Fin (r + 2) → ℂ) ℂ),
    W ∈ complexWhittakerModel (r + 1) (d :: ds) a →
    V ∈ complexWhittakerModel (r + 1) es (-a) →
    HasEqualJacquetExpansion d ds es a D W V Φ ∧
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (complexEqualIntegrand W V Φ s) D.measure ∧
      Integrable (complexEqualIntegrand (ArchimedeanLocal.dualFunction (r + 2) W)
        (ArchimedeanLocal.dualFunction (r + 2) V) (complexFourierTransform a Φ) s) D.measure

/-- At a fixed rank index, the smaller equal-rank theorem and adjacent expansion data
give the adjacent-rank theorem. -/
theorem complexLocalAdjacentAtRank_of_expansion_data
    (hdata : ComplexLocalAdjacentJacquetDataStatement) (r : ℕ)
    (hsmall : ComplexLocalEqualAtRankStatement r) : ComplexLocalAdjacentAtRankStatement r := by
  intro xs es hx he a D W V hW hV
  rcases xs with _ | ⟨d, ds⟩
  · simp at hx
  · have hd : ds.length = r + 1 := Nat.succ.inj hx
    obtain ⟨hE, hC⟩ := hdata r d ds es hd he a D W V hW hV
    exact complexLocalAdjacentJacquetExpansionReduction r d ds es hd he hsmall a D W V hE hC

/-- The adjacent-rank theorem and equal-rank expansion data give the equal-rank successor. -/
theorem complexLocalEqualAtRank_succ_of_expansion_data
    (hdata : ComplexLocalEqualJacquetDataStatement) (r : ℕ)
    (hAdjacent : ComplexLocalAdjacentAtRankStatement r) : ComplexLocalEqualAtRankStatement (r + 1) := by
  intro xs es hx he a D W V Φ hW hV
  rcases xs with _ | ⟨d, ds⟩
  · simp at hx
  · have hd : ds.length = r + 1 := Nat.succ.inj hx
    obtain ⟨hE, hC⟩ := hdata r d ds es hd he a D W V Φ hW hV
    obtain ⟨σ, M, Md, hK, hKd, hM, hMd, hEq, hEqd, hFE⟩ :=
      complexLocalEqualJacquetExpansionReduction r d ds es hd he hAdjacent a D W V Φ hE hC
    have hOpen : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
    exact ⟨σ, M, Md, hK, hKd, differentiableOn_complexEqualIntegral D W V Φ hOpen hK,
      differentiableOn_complexEqualIntegral D (ArchimedeanLocal.dualFunction (r + 2) W)
        (ArchimedeanLocal.dualFunction (r + 2) V) (complexFourierTransform a Φ) hOpen hKd,
      hM, hMd, hEq, hEqd, hFE⟩

/-- The paired expansion data for both steps imply the exact all-rank equal equation. -/
def ComplexLocalJacquetInductionReductionStatement : Prop :=
  ComplexLocalAdjacentJacquetDataStatement →
  ComplexLocalEqualJacquetDataStatement →
  ComplexLocalEqualFunctionalEquationStatement

theorem complexLocalJacquetInductionReduction : ComplexLocalJacquetInductionReductionStatement := by
  intro hAdjacent hEqual
  apply complexLocalEqualFunctionalEquationStatement_iff.mpr
  intro r
  induction r with
  | zero =>
      exact complexLocalEqualRankZero
  | succ r ih =>
      exact complexLocalEqualAtRank_succ_of_expansion_data hEqual r
        (complexLocalAdjacentAtRank_of_expansion_data hAdjacent r ih)

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
