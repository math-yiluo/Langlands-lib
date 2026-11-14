import Langlands.Representation.RankinSelberg.TwoBlockLowerDiagonalFourier
import Langlands.AllField.HarmonicAnalysis.SchwartzBruhatValuationBoundsProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData
/-! Diagonal Fourier reduction and coordinate support for the lower integrand. -/

noncomputable section

open MeasureTheory Matrix
open scoped BigOperators NNReal

namespace Langlands.AllField.HarmonicAnalysis.TwoBlockRowPartialFourier
open Langlands.HarmonicAnalysis.TwoBlockRowPartialFourier
open Langlands.AllField.HarmonicAnalysis.TwoBlockRowPartialFourier
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement exists_rowSchwartz_order_lower_bound padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

section Diagonal



end Diagonal

end Langlands.AllField.HarmonicAnalysis.TwoBlockRowPartialFourier

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement exists_rowSchwartz_order_lower_bound padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF

/-- Compact support bounds below the order of every nonzero coordinate of a row
where a Schwartz–Bruhat function is nonzero. -/
theorem exists_rowSchwartz_order_lower_bound 
    (F : Type uF) [Field F] (T : LocalFieldData F) {N : ℕ}
    (Φ : letI := T.topology; SchwartzBruhat (Fin N → F)) :
    ∃ M : ℕ, ∀ z : Fin N → F, Φ z ≠ 0 →
      ∀ i, z i ≠ 0 → -(M : ℤ) ≤ T.ord (z i) := by
  let := T.topology
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  have hi (i : Fin N) : ∃ n : ℕ, ∀ z : Fin N → F,
      Φ z ≠ 0 → z i ≠ 0 → -(n : ℤ) ≤ T.ord (z i) := by
    obtain ⟨B, hB⟩ := Φ.hasCompactSupport.exists_bound_of_continuousOn
      (T.continuous_normalizedAbs.comp (continuous_apply i)).continuousOn
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hq
    refine ⟨n, fun z hz hzi => ?_⟩
    have h1 := hB _ (subset_tsupport _ hz)
    dsimp only [Function.comp_apply] at h1
    rw [Real.norm_of_nonneg (T.normalizedAbs_nonneg _),
      T.normalizedAbs_of_ne_zero hzi] at h1
    by_contra hlt
    have h2 : (T.residueCardinality : ℝ) ^ (n : ℤ) ≤
        (T.residueCardinality : ℝ) ^ (-T.ord (z i)) :=
      zpow_le_zpow_right₀ hq.le (by omega)
    rw [zpow_natCast] at h2
    linarith
  choose ns hns using hi
  refine ⟨∑ i, ns i, fun z hz i hzi => ?_⟩
  have hle : ns i ≤ ∑ j, ns j := Finset.single_le_sum (fun j _ => Nat.zero_le (ns j))
    (Finset.mem_univ i)
  have h := hns i z hz hzi
  exact le_trans (by exact_mod_cast neg_le_neg (Int.ofNat_le.mpr hle)) h

end Langlands.AllField.HarmonicAnalysis

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe uF

/-- The inverse absolute value of a finite product of units has at most
exponential growth in the sum of their absolute orders. -/
theorem normalizedAbs_prod_inv_le_order_size 
    {F : Type uF} [Field F] (T : LocalFieldData F) {ι : Type*} [Fintype ι]
    (d : ι → Fˣ) :
    (T.normalizedAbs (∏ i, (d i : F)))⁻¹ ≤
      (T.residueCardinality : ℝ) ^ (∑ i, (T.ord (d i : F)).natAbs) := by
  classical
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  have hprod : T.normalizedAbs (∏ i, (d i : F)) =
      ∏ i, T.normalizedAbs (d i : F) := by
    change (T.normalizedAbsHom (∏ i, (d i : F)) : ℝ) = _
    rw [map_prod, NNReal.coe_prod]
    rfl
  rw [hprod, ← Finset.prod_inv_distrib]
  calc
    _ ≤ ∏ i, (T.residueCardinality : ℝ) ^ (T.ord (d i : F)).natAbs := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact inv_nonneg.mpr (T.normalizedAbs_nonneg _)
      · intro i _
        rw [T.normalizedAbs_of_ne_zero (d i).ne_zero, ← zpow_neg, neg_neg,
          ← zpow_natCast]
        exact zpow_le_zpow_right₀ hq.le Int.le_natAbs
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

end Langlands.LocalFieldData

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding
open Langlands.RankinSelberg.TwoBlockLowerUnfolding hiding exists_partialSection_diagonal_bounds groupIntegrand groupIntegrand_def groupIntegrand_lowerBlockUnipotent_mul integrand integrand_mk integrand_mk_eq_groupIntegrand isTopologicalRing_carrier partialSection partialSection_apply partialSection_diagonal partialSection_lowerBlockUnipotent_mul rowMeasure_map_vecMul_upperUnipotent scalarSection_lowerBlockUnipotent_mul sigmaFinite_additiveHaarMeasure whittaker_blockRotation_lowerBlockUnipotent_mul
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement exists_rowSchwartz_order_lower_bound padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis.TwoBlockRowPartialFourier
open Langlands.AllField.HarmonicAnalysis.TwoBlockRowPartialFourier

universe uF

variable {F : Type uF} [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
  [@BorelSpace F (⟨⟩ : LocalFieldData F).topology _]
variable (ψ : UnitaryAdditiveCharacter F)
variable (μ : AdditiveHaarMeasure F)
variable (Φ : SchwartzBruhat (Fin (t + 1) → F))

/-- Exact diagonal formula for the actual lower partial Fourier factor. -/
theorem partialSection_diagonal (d : Fin (t + 1) → Fˣ) :
    partialSection h ψ μ Φ (Iwasawa.diagonalUnits d) =
      ((⟨⟩ : LocalFieldData F).normalizedAbs
        (∏ i : Fin (m 0 + 1), (d ((succBlockShape m h).index 0 i) : F)) : ℂ)⁻¹ *
      (rowPartialFourierIntegral ψ μ (succBlockEquiv h) Φ
        (fun i => zeta (m 0) i * (d ((succBlockShape m h).index 0 i) : F)⁻¹)
        (fun j => eta (m 1) j * (d ((succBlockShape m h).index 1 j) : F))) := by
  have : SecondCountableTopology F := (⟨⟩ : LocalFieldData F).secondCountableTopology
  have := sigmaFinite_additiveHaarMeasure μ
  have hχ (c : F) (hc : c ≠ 0) :
      μ.measure.map (fun x => c * x) =
        ((⟨⟩ : LocalFieldData F).normalizedAbsHom c)⁻¹ • μ.measure :=
    padicScalarHaarScaling F (⟨⟩ : LocalFieldData F) μ.measure (Units.mk0 c hc)
  change rowPartialFourierIntegral ψ μ (succBlockEquiv h)
    (fun x => Φ (x ᵥ* (Iwasawa.diagonalUnits d).val)) (zeta (m 0)) (eta (m 1)) = _
  simpa only [succBlockEquiv_inl, succBlockEquiv_inr,
    Langlands.LocalFieldData.normalizedAbsHom_coe] using
    rowPartialFourierIntegral_diagonal (⟨⟩ : LocalFieldData F).normalizedAbsHom ψ μ hχ
      (succBlockEquiv h) d Φ (zeta (m 0)) (eta (m 1))

/-- Uniform row-factor bound and the two endpoint order cutoffs on diagonal matrices.
The supplied self-dual measure is retained. -/
theorem exists_partialSection_diagonal_bounds
    (hsd : letI := (⟨⟩ : LocalFieldData F).fieldT2
      letI : NonarchimedeanRing F := by
        convert! ValuativeRel.nonarchimedeanRing F
        exact Valuation.toTopologicalSpace_eq _
      IsSelfDual ψ μ) :
    ∃ (C : ℝ) (M : ℕ), 0 < C ∧ ∀ d : Fin (t + 1) → Fˣ,
      ‖partialSection h ψ μ Φ (Iwasawa.diagonalUnits d)‖ ≤
        C * ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
          (∑ j, ((⟨⟩ : LocalFieldData F).ord (d j : F)).natAbs) ∧
      (partialSection h ψ μ Φ (Iwasawa.diagonalUnits d) ≠ 0 →
        (⟨⟩ : LocalFieldData F).ord (d ((succBlockShape m h).index 0 0) : F) ≤ M ∧
        -(M : ℤ) ≤ (⟨⟩ : LocalFieldData F).ord
          (d ((succBlockShape m h).index 1 (Fin.last (m 1))) : F)) := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F := T.fieldT2
  have : TotallyDisconnectedSpace F := by
    let : NonarchimedeanRing F := by
      convert! ValuativeRel.nonarchimedeanRing F
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  have := sigmaFinite_additiveHaarMeasure μ
  let Ψ := partialFourierSchwartz ψ μ hsd (succBlockEquiv h) Φ
  obtain ⟨C₀, hC₀⟩ := Ψ.continuous.bounded_above_of_compact_support Ψ.hasCompactSupport
  obtain ⟨M, hM⟩ := exists_rowSchwartz_order_lower_bound F T Ψ
  refine ⟨max C₀ 1, M, lt_max_of_lt_right one_pos, fun d => ?_⟩
  let z := join (succBlockEquiv h)
    (fun i => zeta (m 0) i * (d ((succBlockShape m h).index 0 i) : F)⁻¹)
    (fun j => eta (m 1) j * (d ((succBlockShape m h).index 1 j) : F))
  have heq : partialSection h ψ μ Φ (Iwasawa.diagonalUnits d) =
      (T.normalizedAbs
        (∏ i : Fin (m 0 + 1), (d ((succBlockShape m h).index 0 i) : F)) : ℂ)⁻¹ *
        Ψ z := by
    rw [partialSection_diagonal]
    simp only [Ψ, z, partialFourierSchwartz_join]
    rfl
  have habs := T.normalizedAbs_prod_inv_le_order_size
    (fun i : Fin (m 0 + 1) => d ((succBlockShape m h).index 0 i))
  have hsize : (∑ i : Fin (m 0 + 1),
      (T.ord (d ((succBlockShape m h).index 0 i) : F)).natAbs) ≤
      ∑ j, (T.ord (d j : F)).natAbs := by
    rw [← Equiv.sum_comp (succBlockEquiv h) (fun j => (T.ord (d j : F)).natAbs),
      Fintype.sum_sum_type]
    simp only [succBlockEquiv_inl, succBlockEquiv_inr]
    omega
  have hq : (1 : ℝ) ≤ T.residueCardinality := by
    exact_mod_cast (le_of_lt T.residueCardinality_gt_one)
  have hfactor : (T.normalizedAbs
      (∏ i : Fin (m 0 + 1), (d ((succBlockShape m h).index 0 i) : F)))⁻¹ ≤
      (T.residueCardinality : ℝ) ^ (∑ j, (T.ord (d j : F)).natAbs) :=
    habs.trans (pow_le_pow_right₀ hq hsize)
  constructor
  · rw [heq, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (T.normalizedAbs_nonneg _)]
    calc
      _ ≤ (T.residueCardinality : ℝ) ^ (∑ j, (T.ord (d j : F)).natAbs) *
          max C₀ 1 := mul_le_mul hfactor ((hC₀ z).trans (le_max_left _ _))
            (norm_nonneg _) (by positivity)
      _ = _ := mul_comm _ _
  · intro hne
    have hz : Ψ z ≠ 0 := (mul_ne_zero_iff.mp (heq ▸ hne)).2
    have hfirst : z ((succBlockShape m h).index 0 0) =
        (d ((succBlockShape m h).index 0 0) : F)⁻¹ := by
      dsimp only [z]
      rw [join_succBlockEquiv_index_zero]
      simp [zeta]
    have hlast : z ((succBlockShape m h).index 1 (Fin.last (m 1))) =
        (d ((succBlockShape m h).index 1 (Fin.last (m 1))) : F) := by
      dsimp only [z]
      rw [join_succBlockEquiv_index_one]
      simp [eta]
    have h0 := hM z hz ((succBlockShape m h).index 0 0)
      (by rw [hfirst]; exact inv_ne_zero (d _).ne_zero)
    have h1 := hM z hz ((succBlockShape m h).index 1 (Fin.last (m 1)))
      (by rw [hlast]; exact (d _).ne_zero)
    rw [hfirst, T.ord_inv] at h0
    rw [hlast] at h1
    exact ⟨by change T.ord _ ≤ (M : ℤ); omega, h1⟩

end Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding
