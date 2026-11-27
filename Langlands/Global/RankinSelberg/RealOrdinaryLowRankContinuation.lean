import Langlands.Global.RankinSelberg.RealCanonicalOrdinaryDeformation
import Langlands.Global.RankinSelberg.RealDiscreteRankTwoWhittaker
import Langlands.Global.RankinSelberg.RealLocalUniformPositiveEqualContinuationProof
import Langlands.Global.RankinSelberg.RealRankTwoWhittakerDescent
import Langlands.Global.RankinSelberg.RealTemperedCharacterBound

/-! # Ordinary real normalized continuation through rank two -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal RealIwasawa RealBlockParameters RealPrincipalSeries RealJacquet
open RealTemperedWhittaker

/-- The exact scalar tempered bound holds in total rank two for every real block list. -/
theorem realTemperedWhittakerBoundAtRank_one : RealTemperedWhittakerBoundAtRank 1 := by
  intro ds hr him a W hW ε hε
  by_cases hwt : ∀ d : ComplexCharacterData, RealBlock.induced d ∈ ds → d.weight = 0
  · exact realTemperedWhittakerCharacterBound 1 ds hr hwt him a W hW ε hε
  push Not at hwt
  obtain ⟨d, hd, hw⟩ := hwt
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hd
  have he (xs : List RealBlock) (hx : realRank xs = 0) : xs = [] := by
    cases xs with
    | nil => rfl
    | cons x xs =>
      cases x <;> simp [realRank_cons, RealBlock.rank] at hx
  rw [Langlands.Archimedean.RealLeviSlices.realRank_append, realRank_cons, RealBlock.rank] at hr
  have hp := he pre (by omega)
  have hq := he post (by omega)
  subst pre post
  have hu : d.exponent.re = 0 := him (.induced d) List.mem_cons_self
  obtain ⟨C, hC, hBound⟩ :=
    RealDiscreteRankTwoWhittaker.realDiscreteWhittakerBound d hw a W hW
  refine ⟨C, hC, fun y k => (hBound y k).trans ?_⟩
  have hmod : torusModularLog 2 y = y 0 - y 1 := by
    rw [torusModularLog_apply, Fin.sum_univ_two]
    norm_num
    ring
  rw [hu, zero_mul, add_zero, hmod]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
  exact le_add_of_nonneg_right (mul_nonneg hε.le (Finset.sum_nonneg fun _ _ => abs_nonneg _))

private theorem lowRankAscending_le {r : ℕ} (hr : r ≤ 1) (ds : List RealBlock)
    (hd : realRank ds = r + 1) (a : ℝˣ) :
    realUniformWhittakerModel r (ascendingExpand ds) a ≤ realWhittakerModel r ds a := by
  have h := RealUniformWhittaker.model_le_model (r := r) (ascendingExpand ds) a
  rcases show r = 0 ∨ r = 1 by omega with rfl | rfl
  · obtain ⟨c, rfl⟩ := RealRankZero.eq_singleton_of_realRank_eq_one hd
    exact h
  · rwa [realRankTwoWhittakerDescent ds hd a] at h

private theorem lowRankFamily_on_imaginaryAxis {r t : ℕ} (hr : r ≤ 1) (ht : t ≤ 1)
    {ds es : List RealBlock} (hd : realRank ds = r + 1) (he : realRank es = t + 1) {a : ℝˣ}
    {I : (Langlands.GeneralLinear (r + 1) ℝ → ℂ) →
      (Langlands.GeneralLinear (t + 1) ℝ → ℂ) → ℂ → ℂ}
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ} {V : Langlands.GeneralLinear (t + 1) ℝ → ℂ}
    (h : HasRealOrdinaryHolomorphicTestFamilyOn ∅ ds es a I W V) :
    HasRealOrdinaryHolomorphicTestFamilyOn {z : ℂ | z.re = 0} ds es a I W V := by
  obtain ⟨U, U', σ, hU, hU', hAscending, _, hHol⟩ := h
  refine ⟨U, U', σ, hU, hU', hAscending, fun z hz => ?_, hHol⟩
  exact ⟨lowRankAscending_le hr _ ((realRank_deformBlocks ds z).trans hd) a (hAscending z hz.1).1,
    lowRankAscending_le ht _ ((realRank_deformBlocks es z).trans he) (-a) (hAscending z hz.1).2⟩

/-- The two clauses of real ordinary normalized continuation for groups of total rank at most two. -/
def RealOrdinaryLowRankContinuationStatement : Prop :=
  (∀ (r t : ℕ) (h : t < r), r ≤ 1 → ∀ (ds es : List RealBlock),
    realRank ds = r + 1 → realRank es = t + 1 → ∀ (a : ℝˣ) (D : RealQuotientMeasureData t),
      HasEntireOrdinaryNormalizations (realOrdinaryUnequalTest h ds es a D) (realPairLFactor ds es)) ∧
    ∀ (r : ℕ), r ≤ 1 → ∀ (ds es : List RealBlock),
      realRank ds = r + 1 → realRank es = r + 1 → ∀ (a : ℝˣ) (D : RealQuotientMeasureData r),
        HasEntireOrdinaryNormalizations (realOrdinaryEqualTest r ds es a D) (realPairLFactor ds es)

theorem realOrdinaryLowRankContinuation : RealOrdinaryLowRankContinuationStatement := by
  have hRange := RealUniformCanonicalRange.realUniformCanonicalRangePremise
  have hEval := RealUniformCanonicalRange.realCanonicalStandardEvaluationPremise
  have hEqual := realLocalEqualCharacterGrowth_of_canonicalPremises hRange hEval
  have hAdjacent := realAdjacentFromEqualGrowth hRange (realOrthogonalCompactProjectionPremise 0) (hEqual 0)
  have hFamilies := realOrdinaryHolomorphicTestFamiliesOn_of_ascending ∅ hRange (by simp)
  constructor
  · rintro r t h hr ds es hd he a D ⟨W, V⟩
    have hr' : r = 1 := by omega
    have ht' : t = 0 := by omega
    subst r t
    exact realOrdinaryUnequalBlockAssembly h hAdjacent realTemperedWhittakerBoundAtRank_one
      realTemperedWhittakerBoundAtRank_zero hd he a D
      (lowRankFamily_on_imaginaryAxis (by decide) (by decide) hd he
        (hFamilies.1 1 0 h ds es hd he a D W V W.2 V.2))
  · intro r hr ds es hd he a D
    rcases show r = 0 ∨ r = 1 by omega with rfl | rfl
    · exact (rankOneOrdinaryNormalizedTests.1 ds es hd he a D).1
    · rintro ⟨W, V, Φ⟩
      exact realOrdinaryEqualBlockAssembly (hEqual 1) realTemperedWhittakerBoundAtRank_one hd he a D Φ
        (lowRankFamily_on_imaginaryAxis (by decide) (by decide) hd he
          (hFamilies.2 1 (by decide) ds es hd he a D W V Φ W.2 V.2))

end Langlands.Global.RankinSelbergGlobal
