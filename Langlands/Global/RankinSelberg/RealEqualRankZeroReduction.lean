import Langlands.Global.RankinSelberg.ArchimedeanFunctionalEquationStatement
import Langlands.Global.RankinSelberg.RealRankZeroEqual

/-! # The rank-one case of the equal-rank real-place functional equation

`RealEqualFunctionalEquationStatement` is split by the rank index `r` into the propositions
`RealEqualAtRankStatement r`. The case `r = 0` (`GL₁ × GL₁`) follows from the real Tate
statement `RealArchimedeanTateStatement`. Hence, given the real Tate statement, the equal-rank
statement at all positive ranks implies the full equal-rank statement. See the paired
Markdown.
-/

noncomputable section

universe u

open NumberField MeasureTheory
open Langlands.Global.HeckeFunctionalEquation Langlands.LocalFactor.Archimedean

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal

local instance realEqualRankZeroRealGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
local instance realEqualRankZeroRealGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
local instance realEqualRankZeroRealNMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
local instance realEqualRankZeroRealNBorel (n : ℕ) :
    BorelSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
local instance realEqualRankZeroRealQMeasurable (n : ℕ) :
    MeasurableSpace (RankinSelberg.LeftUnipotentQuotient n ℝ) := borel _
local instance realEqualRankZeroRealQBorel (n : ℕ) :
    BorelSpace (RankinSelberg.LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

/-- `RealEqualFunctionalEquationStatement` at the single rank index `r` (the group
`GL_(r+1)`): the same quantifiers, hypotheses and conclusions, with `r` fixed. -/
def RealEqualAtRankStatement (r : ℕ) : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (T Td T' Td' : Automorphic.CuspidalOperatorRealization F r),
    Automorphic.OperatorRealization.IsContragredientOf Td.realization T.realization →
    Automorphic.OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ),
    IsRealAdditiveComponent ψ v.1 v.2 a →
  ∀ (d d' dd dd' : List RealBlock),
    Automorphic.OperatorRealization.HasRealPlaceParameter T.realization v d →
    Automorphic.OperatorRealization.HasRealPlaceParameter T'.realization v d' →
    Automorphic.OperatorRealization.HasRealPlaceParameter Td.realization v dd →
    Automorphic.OperatorRealization.HasRealPlaceParameter Td'.realization v dd' →
  ∀ (D : RealQuotientMeasureData r) (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ),
    IsRealPlaceWhittaker F T ψ.complex v W →
    IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' →
  ∃ (σ : ℝ) (M Md : ℂ → ℂ),
    (∀ s : ℂ, σ < s.re → Integrable (realEqualIntegrand W W' Φ s) D.measure) ∧
    (∀ s : ℂ, σ < s.re →
      Integrable (realEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
        (ArchimedeanLocal.dualFunction (r + 1) W') (realFourierTransform a Φ) s)
        D.measure) ∧
    DifferentiableOn ℂ (realEqualIntegral D W W' Φ) {s : ℂ | σ < s.re} ∧
    DifferentiableOn ℂ (realEqualDualIntegral a D W W' Φ) {s : ℂ | σ < s.re} ∧
    MeromorphicOn M Set.univ ∧ MeromorphicOn Md Set.univ ∧
    (∀ s : ℂ, σ < s.re → realEqualIntegral D W W' Φ s = M s) ∧
    (∀ s : ℂ, σ < s.re → realEqualDualIntegral a D W W' Φ s = Md s) ∧
    ∀ᶠ s in Filter.codiscrete ℂ,
      ((realPairLFactor d d').denominator s)⁻¹ * Md (1 - s) =
        realMinusOneScalar T' v ^ r *
          (realPairEpsilon d d' a (NNReal.sqrt ‖(a : ℝ)‖₊)
            (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) s : ℂ) *
          ((realPairLFactor dd dd').denominator (1 - s))⁻¹ * M s

/-- The equal-rank real-place statement is the conjunction of its instances at every rank. -/
theorem realEqualFunctionalEquationStatement_iff :
    RealEqualFunctionalEquationStatement.{u} ↔ ∀ r : ℕ, RealEqualAtRankStatement.{u} r := by
  constructor
  · intro h r F _ _ _ ψ hψ
    exact h F ψ hψ r
  · intro h F _ _ _ ψ hψ r
    exact h r F ψ hψ

/-- **The `GL₁ × GL₁` case.** The real Tate statement implies the equal-rank real-place
statement at rank index `0`. -/
theorem realEqualAtRankStatement_zero (hTate : Langlands.LocalFactor.RealArchimedeanTateStatement) :
    RealEqualAtRankStatement.{u} 0 := by
  intro F _ _ _ ψ _ T Td T' Td' hTd hTd' v a _ d d' dd dd' hd hd' hdd hdd' D W W' Φ hW hW'
  exact RealRankZero.realEqual_rankZero_global hTate ψ.complex T Td T' Td' hTd hTd' v a
    d d' dd dd' hd hd' hdd hdd' D W W' Φ hW hW'

/-- **Rank-one reduction of the equal-rank real-place functional equation.** Given the real
Tate statement, the equal-rank real-place statement at every positive rank index implies the
full `RealEqualFunctionalEquationStatement`. -/
def RealEqualRankZeroReductionStatement : Prop :=
  Langlands.LocalFactor.RealArchimedeanTateStatement →
    (∀ r : ℕ, 0 < r → RealEqualAtRankStatement.{u} r) →
      RealEqualFunctionalEquationStatement.{u}

/-- Proof of `RealEqualRankZeroReductionStatement`: rank index `0` comes from
`realEqualAtRankStatement_zero`, the positive ranks from the hypothesis. -/
theorem realEqualRankZeroReductionStatement : RealEqualRankZeroReductionStatement.{u} := by
  intro hTate hpos
  refine realEqualFunctionalEquationStatement_iff.mpr fun r => ?_
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact realEqualAtRankStatement_zero hTate
  · exact hpos r hr

end Langlands.Global.RankinSelbergGlobal
