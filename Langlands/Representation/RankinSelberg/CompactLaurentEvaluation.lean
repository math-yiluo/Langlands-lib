import Langlands.Representation.RankinSelberg.EqualRankCompactLaurent

/-! # Evaluating compact equal-rank integrals at convergent parameters -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  (μ : letI := T.topology
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    Measure (LeftUnipotentQuotient n F.Carrier))

/-- The finite Laurent polynomial of the actual equal-rank integrand at zero,
when that integrand has compact quotient support. -/
def compactEqualRankLaurent :
    letI := T.topology
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
      (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
      HasCompactSupport (equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ 0) →
      LaurentCoefficients := by
  let := T.topology
  intro ψ W W' Φ hc
  exact compactSliceLaurent T μ _ hc

/-- The finite slice polynomial evaluates to the actual integral at every
parameter at which that integral converges. -/
theorem eval_compactEqualRankLaurent :
    letI := T.topology
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
      (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier))
      (hc : HasCompactSupport (equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ 0))
      (s : ℂ),
      EqualRankConverges ψ (normalizedAbsoluteValue T) μ W W' Φ s →
      RatFunc.eval (RingHom.id ℂ) (spectralPoint T.residueCardinality s)
          (laurentToRatFunc (compactEqualRankLaurent T μ ψ W W' Φ hc)) =
        equalRankIntegral ψ (normalizedAbsoluteValue T) μ W W' Φ s := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F.Carrier)
  intro ψ W W' Φ hc s hs
  classical
  let c := equalRankSliceCoefficient T μ ψ W W' Φ
  have hfin : (Function.support c).Finite :=
    finite_support_sliceCoefficient_of_hasCompactSupport T μ _ hc
  have heval := (laurentToRatFunc_regular_and_eval
    (spectralUnit (Nat.zero_lt_one.trans T.residueCardinality_gt_one) s)
    (compactEqualRankLaurent T μ ψ W W' Φ hc)).2
  simp only [coe_spectralUnit] at heval
  rw [heval]
  have hsum := (equalRankSliceExpansion F T n μ ψ W W' Φ s hs).2.2
  have hzero : ∀ m ∉ hfin.toFinset, c m * spectralPoint T.residueCardinality s ^ m = 0 := by
    intro m hm
    have hcm : c m = 0 := by
      by_contra hne
      exact hm (hfin.mem_toFinset.mpr hne)
    rw [hcm, zero_mul]
  rw [hsum.unique (hasSum_sum_of_ne_finset_zero hzero)]
  simp only [compactEqualRankLaurent, compactSliceLaurent, map_sum, map_mul,
    laurentEval_C, laurentEval_T, coe_spectralUnit]
  rfl

/-- Convergence on a right half-plane makes this particular finite Laurent
polynomial a rational continuation of the original integral. -/
theorem compactEqualRankLaurent_continuation :
    letI := T.topology
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
      (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier))
      (hc : HasCompactSupport (equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ 0)),
      (∃ a : ℝ, ∀ s : ℂ, a < s.re →
        EqualRankConverges ψ (normalizedAbsoluteValue T) μ W W' Φ s) →
      HasRationalContinuation T.residueCardinality
        (equalRankIntegral ψ (normalizedAbsoluteValue T) μ W W' Φ)
        (laurentToRatFunc (compactEqualRankLaurent T μ ψ W W' Φ hc)) := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F.Carrier)
  intro ψ W W' Φ hc ⟨a, ha⟩
  refine ⟨a, fun s hs => ⟨?_, (eval_compactEqualRankLaurent T μ ψ W W' Φ hc s (ha s hs)).symm⟩⟩
  exact laurentToRatFunc_regular
    (spectralUnit (Nat.zero_lt_one.trans T.residueCardinality_gt_one) s) _

/-- A supplied continuation agrees with the compact integral at any supplied
convergent parameter, including parameters outside the initial half-plane.
The conclusion includes regularity, so evaluation is not used at a pole. -/
theorem equalRankContinuation_regular_and_eval_of_hasCompactSupport :
    letI := T.topology
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
      (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
      HasCompactSupport (equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ 0) →
      (∃ a : ℝ, ∀ s : ℂ, a < s.re →
        EqualRankConverges ψ (normalizedAbsoluteValue T) μ W W' Φ s) →
      ∀ R : RationalFunctions, HasRationalContinuation T.residueCardinality
        (equalRankIntegral ψ (normalizedAbsoluteValue T) μ W W' Φ) R →
      ∀ s : ℂ, EqualRankConverges ψ (normalizedAbsoluteValue T) μ W W' Φ s →
        R.denom.eval (spectralPoint T.residueCardinality s) ≠ 0 ∧
          RatFunc.eval (RingHom.id ℂ) (spectralPoint T.residueCardinality s) R =
            equalRankIntegral ψ (normalizedAbsoluteValue T) μ W W' Φ s := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F.Carrier)
  intro ψ W W' Φ hc hconv R hR s hs
  have hL := compactEqualRankLaurent_continuation T μ ψ W W' Φ hc hconv
  have heq := HasRationalContinuation.unique T.residueCardinality_gt_one hL hR
  rw [← heq]
  exact ⟨laurentToRatFunc_regular
    (spectralUnit (Nat.zero_lt_one.trans T.residueCardinality_gt_one) s) _,
    eval_compactEqualRankLaurent T μ ψ W W' Φ hc s hs⟩

end Langlands.RankinSelberg
