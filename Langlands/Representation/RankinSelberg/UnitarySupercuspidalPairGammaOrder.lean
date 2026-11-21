import Langlands.Representation.RankinSelberg.PairGammaOrder
import Langlands.Representation.RankinSelberg.SupercuspidalEulerFamily

/-! # Gamma orders for a unitary supercuspidal pair -/

noncomputable section

universe uF uV uW

set_option autoImplicit false

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis LocalFactor Polynomial Whittaker
open SupercuspidalLFactorCharacterization (isGeneric_of_isSupercuspidal)

/-- A unitary supercuspidal pair has no gamma zeros off the imaginary axis.
The order at zero is the indicator of contragredience of the two members. -/
def UnitarySupercuspidalPairGammaOrderStatement : Prop := by
  classical
  exact ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) (r n : ℕ),
    letI := F.canonicalTopologicalData.topology
    ∀ (A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r + 1))
      (B : SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := n + 1)),
      IsUnitarizable A.obj.representation → IsUnitarizable B.obj.representation →
      ∀ (G : RatFunc ℂ),
        IsPadicSymmetricGammaFactor F ψ ν.val A.obj.representation B.obj.representation G →
        let γ := rationalSpectralValue F.canonicalTopologicalData.residueCardinality G
        (∀ z : ℂ, MeromorphicAt γ z) ∧
        (∀ z : ℂ, z.re ≠ 0 → meromorphicOrderAt γ z ≤ 0) ∧
        meromorphicOrderAt γ 0 =
          if IsRankContragredient A.obj.representation B.obj.representation then 1 else 0

set_option maxHeartbeats 800000 in
theorem unitarySupercuspidalPairGammaOrder : UnitarySupercuspidalPairGammaOrderStatement.{uF, uV, uW} := by
  classical
  intro p _ F ψ ν r n
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro A B hAu hBu G hΓ
  let π := A.obj.representation
  let σ := B.obj.representation
  have hπ := isGeneric_of_isSupercuspidal F ψ r A.obj A.property.1 A.property.2
  have hσ := isGeneric_of_isSupercuspidal F ψ n B.obj B.property.1 B.property.2
  let D := supercuspidalPairEuler supercuspidalEqualRankLFactor ψ ν π σ
    A.property.1 B.property.1 A.property.2 B.property.2 hAu hBu
  let P := D.data.polynomial
  let Pd := genericSymmetricDualLPolynomial F ψ ν.val π σ hπ hσ
  let ε := genericSymmetricEpsilonData F ψ ν.val ν.property π σ hπ hσ
  have hPd : IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
      (inverseTransposePullback π) (inverseTransposePullback σ) Pd :=
    genericSymmetricDualLPolynomial_isPadic F ψ ν.val π σ hπ hσ
  have hP : genericSymmetricLPolynomial F ψ ν.val π σ hπ hσ = P :=
    (genericSymmetricLPolynomial_isPadic F ψ ν.val π σ hπ hσ).unique D.certified
  have he : G = rationalGammaExpression (residueReflection F) ε.1 ε.2 P Pd :=
    (genericSymmetricGammaFactor_eq F ψ ν.val ν.property π σ hπ hσ hΓ).symm.trans
      ((genericSymmetricGammaFactor_eq_expression F ψ ν.val ν.property π σ hπ hσ).trans
        (congrArg (fun Q => rationalGammaExpression (residueReflection F) ε.1 ε.2 Q Pd) hP))
  have hPd0 := ne_zero_of_coeff_zero_eq_one hPd.coeff_zero
  have horder (z : ℂ) :
      meromorphicOrderAt (rationalSpectralValue T.residueCardinality G) z =
        ((P.rootMultiplicity (spectralPoint T.residueCardinality z) : ℤ) -
          (Pd.rootMultiplicity (spectralPoint T.residueCardinality (1 - z)) : ℤ) : ℤ) := by
    rw [he, meromorphicOrderAt_rationalGammaExpression T.residueCardinality
      T.residueCardinality_gt_one _ _ (coe_residueReflection F) _ P Pd
      (ne_zero_of_coeff_zero_eq_one D.certified.coeff_zero) hPd0]
  refine ⟨?_, ?_, ?_⟩
  · intro z
    rw [he]
    exact (meromorphicAt_polynomialGammaExpression T.residueCardinality
      T.residueCardinality_gt_one ε.1 ε.2 P Pd z).congr
      (rationalSpectralValue_eventuallyEq_polynomialGammaExpression T.residueCardinality
        T.residueCardinality_gt_one _ _ (coe_residueReflection F) _ P Pd hPd0 z).symm
  · intro z hz
    have hq0 : 0 < (T.residueCardinality : ℝ) := by
      exact_mod_cast (show 0 < T.residueCardinality from Nat.zero_lt_one.trans T.residueCardinality_gt_one)
    have hn : P.eval (spectralPoint T.residueCardinality z) ≠ 0 := by
      rw [spectralPoint_eq_spectralParameter _ hq0]
      exact fun h => D.data.denominator_ne_zero hz (by
        simpa only [D.data.denominator_eq_eval, D.q_eq] using h)
    rw [horder, rootMultiplicity_eq_zero hn, Nat.cast_zero]
    exact_mod_cast sub_nonpos.mpr (Int.natCast_nonneg _)
  · have hPd1 : Pd.eval (spectralPoint T.residueCardinality 1) ≠ 0 :=
      UnitaryGeneric.unitaryGenericLPolynomialNonvanishing p F (ψ.scale (-1))
        (DominantRankTransport.negatedSelfDualHaar F ψ ν) r n
        (inverseTransposePullback π) (inverseTransposePullback σ)
        (HighlyRamified.isGeneric_inverseTransposePullback F ψ π hπ)
        (hAu.comp _) (HighlyRamified.isGeneric_inverseTransposePullback F ψ σ hσ)
        (hBu.comp _) Pd hPd 1 (by simp)
    have hpoint : spectralPoint T.residueCardinality 0 = 1 := by simp [spectralPoint]
    rw [horder, sub_zero, rootMultiplicity_eq_zero hPd1, Nat.cast_zero, sub_zero, hpoint]
    change ((lPolynomialPoleOrderAtZero D.data.polynomial : ℤ) : WithTop ℤ) = _
    rw [FiniteUnitaryEuler.polynomial, lPolynomialPoleOrderAtZero_prod_one_sub_C_mul_X]
    by_cases hc : IsRankContragredient A.obj.representation B.obj.representation
    · simp [hc, D.one_mem_iff.mpr hc]
    · have hmem : (1 : ℂ) ∉ D.data.parameters := fun h => hc (D.one_mem_iff.mp h)
      simp [hc, hmem]

end Langlands.RankinSelberg
