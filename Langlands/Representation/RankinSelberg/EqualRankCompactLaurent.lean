import Langlands.Representation.RankinSelberg.EqualRankSliceExpansionProof
import Langlands.Representation.RankinSelberg.LaurentEvaluation
import Langlands.Representation.RankinSelberg.MirabolicRowCompactSupport

/-! # Laurent continuation from compact equal-rank quotient support -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  (μ : letI := T.topology
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    Measure (LeftUnipotentQuotient n F.Carrier))

/-- Compact quotient support leaves only finitely many possibly nonzero
determinant-slice integrals, for an arbitrary quotient measure. -/
theorem finite_support_sliceCoefficient_of_hasCompactSupport :
    letI := T.topology
    ∀ (f : LeftUnipotentQuotient n F.Carrier → ℂ),
      HasCompactSupport f → (Function.support (sliceCoefficient T μ f)).Finite := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F.Carrier)
  intro f hf
  have hfin : (determinantOrder T n '' tsupport f).Finite :=
    (hf.image (continuous_determinantOrder T n)).finite_of_discrete
  apply hfin.subset
  intro m hm
  by_contra hnot
  apply hm
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  apply image_eq_zero_of_notMem_tsupport
  intro hxt
  exact hnot ⟨x, hxt, hx⟩

/-- The finite Laurent polynomial of slice integrals of a compactly
supported quotient function, at the residue-normalized determinant order. -/
def compactSliceLaurent :
    letI := T.topology
    ∀ (f : LeftUnipotentQuotient n F.Carrier → ℂ),
      HasCompactSupport f → LaurentCoefficients := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F.Carrier)
  intro f hf
  exact ∑ m ∈ (finite_support_sliceCoefficient_of_hasCompactSupport T μ f hf).toFinset,
    LaurentPolynomial.C (sliceCoefficient T μ f m) * LaurentPolynomial.T m

/-- Compact support at zero and convergence on a right half-plane identify the
actual equal-rank integral there with a finite Laurent polynomial. -/
theorem exists_laurent_equalRankIntegral_of_hasCompactSupport :
    letI := T.topology
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
      (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
      HasCompactSupport (equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ 0) →
      (∃ a : ℝ, ∀ s : ℂ, a < s.re →
        EqualRankConverges ψ (normalizedAbsoluteValue T) μ W W' Φ s) →
      ∃ L : LaurentCoefficients, HasRationalContinuation T.residueCardinality
        (equalRankIntegral ψ (normalizedAbsoluteValue T) μ W W' Φ)
        (laurentToRatFunc L) := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F.Carrier)
  intro ψ W W' Φ hc ⟨a, ha⟩
  classical
  let c := equalRankSliceCoefficient T μ ψ W W' Φ
  have hfin : (Function.support c).Finite :=
    finite_support_sliceCoefficient_of_hasCompactSupport T μ _ hc
  let L := compactSliceLaurent T μ _ hc
  refine ⟨L, a, fun s hs => ?_⟩
  have heval := laurentToRatFunc_regular_and_eval
    (spectralUnit (Nat.zero_lt_one.trans T.residueCardinality_gt_one) s) L
  simp only [coe_spectralUnit] at heval
  refine ⟨heval.1, ?_⟩
  rw [heval.2]
  have hsum := (equalRankSliceExpansion F T n μ ψ W W' Φ s (ha s hs)).2.2
  have hzero : ∀ m ∉ hfin.toFinset, c m * spectralPoint T.residueCardinality s ^ m = 0 := by
    intro m hm
    have hcm : c m = 0 := by
      by_contra hne
      exact hm (hfin.mem_toFinset.mpr hne)
    rw [hcm, zero_mul]
  rw [hsum.unique (hasSum_sum_of_ne_finset_zero hzero)]
  change (∑ m ∈ hfin.toFinset, c m * spectralPoint T.residueCardinality s ^ m) =
    laurentEval _ L
  simp only [L, compactSliceLaurent, map_sum, map_mul, laurentEval_C, laurentEval_T,
    coe_spectralUnit]
  rfl

/-- Every rational continuation of such a compactly supported family is the
image of a Laurent polynomial, by uniqueness on the right half-plane. -/
theorem exists_laurent_of_equalRankContinuation_hasCompactSupport :
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
        ∃ L : LaurentCoefficients, laurentToRatFunc L = R := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F.Carrier)
  intro ψ W W' Φ hc hconv R hR
  obtain ⟨L, hL⟩ := exists_laurent_equalRankIntegral_of_hasCompactSupport
    T μ ψ W W' Φ hc hconv
  exact ⟨L, HasRationalContinuation.unique T.residueCardinality_gt_one hL hR⟩

/-- Mirabolic compact translates give Laurent regularity for every row test
vanishing at zero, once the actual integral converges on a right half-plane. -/
theorem HasMirabolicCompactTranslates.exists_laurent_equalRankContinuation :
    letI := T.topology
    letI := T.fieldT2
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI := T.valuativeRel
    letI := T.localField
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (W : WhittakerFunctions ψ n),
      HasMirabolicCompactTranslates W.val →
      ∀ (J : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier)),
      IsCompact (J : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) →
      (∀ g, ∀ j : J, W.val (g * j.val) = W.val g) →
      ∀ (W' : InverseWhittakerFunctions ψ n)
        (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)), Φ 0 = 0 →
      (∃ a : ℝ, ∀ s : ℂ, a < s.re →
        EqualRankConverges ψ (normalizedAbsoluteValue T) μ W W' Φ s) →
      ∀ R : RationalFunctions, HasRationalContinuation T.residueCardinality
        (equalRankIntegral ψ (normalizedAbsoluteValue T) μ W W' Φ) R →
        ∃ L : LaurentCoefficients, laurentToRatFunc L = R := by
  let := T.topology
  let := T.fieldT2
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let := T.valuativeRel
  let := T.localField
  intro ψ W hmir J hJ hfix W' Φ hΦ hc R hR
  exact exists_laurent_of_equalRankContinuation_hasCompactSupport T μ ψ W W' Φ
    (hmir.equalRankIntegrand_hasCompactSupport J hJ hfix W' Φ hΦ _ 0) hc R hR

end Langlands.RankinSelberg
