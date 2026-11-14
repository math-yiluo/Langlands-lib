import Langlands.Representation.RankinSelberg.TwoBlockLowerCompactFourier
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerDiagonalFourier
/-! Compact-uniform partial Fourier estimates for the lower integrand. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement exists_rowSchwartz_order_lower_bound padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe u

end Langlands.AllField.HarmonicAnalysis

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding
open Langlands.RankinSelberg.TwoBlockLowerUnfolding hiding blockRotation_inv_mul_diagonal exists_partialSection_diagonal_bounds exists_partialSection_diagonal_compact_bounds exists_partialSection_rotated_diagonal_compact_bounds exists_partialSection_rotated_torus_compact_bounds groupIntegrand groupIntegrand_def groupIntegrand_lowerBlockUnipotent_mul integrand integrand_mk integrand_mk_eq_groupIntegrand isTopologicalRing_carrier partialSection partialSection_apply partialSection_diagonal partialSection_lowerBlockUnipotent_mul partialSection_mul rowMeasure_map_vecMul_upperUnipotent scalarSection_lowerBlockUnipotent_mul sigmaFinite_additiveHaarMeasure whittaker_blockRotation_lowerBlockUnipotent_mul
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement exists_rowSchwartz_order_lower_bound padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice

universe uF

variable {F : Type uF} [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
  [@BorelSpace F (⟨⟩ : LocalFieldData F).topology _]
variable (ψ : UnitaryAdditiveCharacter F)
variable (μ : AdditiveHaarMeasure F)
variable (Φ : SchwartzBruhat (Fin (t + 1) → F))

omit [@BorelSpace F (⟨⟩ : LocalFieldData F).topology _] in
/-- Moving the last factor of a group product into the Schwartz function. -/
theorem partialSection_mul (g k : GeneralLinear (t + 1) F) :
    partialSection h ψ μ Φ (g * k) =
      partialSection h ψ μ
        (letI := isTopologicalRing_carrier F
         rowTranslate k Φ) g := by
  let := isTopologicalRing_carrier F
  simp only [partialSection, rowTranslate_mul]

/-- One pair of constants works for all compact right translates of the diagonal. -/
theorem exists_partialSection_diagonal_compact_bounds
    (hsd : letI := (⟨⟩ : LocalFieldData F).fieldT2
      letI : NonarchimedeanRing F := by
        convert! ValuativeRel.nonarchimedeanRing F
        exact Valuation.toTopologicalSpace_eq _
      IsSelfDual ψ μ)
    (K : Set (GeneralLinear (t + 1) F))
    (hK : IsCompact K) :
    ∃ (C : ℝ) (M : ℕ), 0 < C ∧
      ∀ (d : Fin (t + 1) → Fˣ) (k : GeneralLinear (t + 1) F), k ∈ K →
      ‖partialSection h ψ μ Φ (Iwasawa.diagonalUnits d * k)‖ ≤
        C * ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
          (∑ j, ((⟨⟩ : LocalFieldData F).ord (d j : F)).natAbs) ∧
      (partialSection h ψ μ Φ (Iwasawa.diagonalUnits d * k) ≠ 0 →
        (⟨⟩ : LocalFieldData F).ord (d ((succBlockShape m h).index 0 0) : F) ≤ M ∧
        -(M : ℤ) ≤ (⟨⟩ : LocalFieldData F).ord
          (d ((succBlockShape m h).index 1 (Fin.last (m 1))) : F)) := by
  classical
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hS := finite_rowTranslate_schwartz_range Φ K hK
  let S := Set.range (fun k : K => rowTranslate k.val Φ)
  let := hS.fintype
  have hb (Ψ : S) := exists_partialSection_diagonal_bounds h ψ μ Ψ.val hsd
  choose Cs Ms hCs hbounds using hb
  obtain ⟨C, hC⟩ := (Set.finite_range Cs).bddAbove
  obtain ⟨M, hM⟩ := (Set.finite_range Ms).bddAbove
  refine ⟨max C 1, M, lt_max_of_lt_right one_pos, fun d k hk => ?_⟩
  let Ψ : S := ⟨rowTranslate k Φ, ⟨⟨k, hk⟩, rfl⟩⟩
  have hΨ := hbounds Ψ d
  have hCM : Cs Ψ ≤ max C 1 := (hC (Set.mem_range_self Ψ)).trans (le_max_left _ _)
  have hMM : Ms Ψ ≤ M := hM (Set.mem_range_self Ψ)
  rw [partialSection_mul]
  constructor
  · exact hΨ.1.trans (mul_le_mul_of_nonneg_right hCM (by positivity))
  · intro hne
    obtain ⟨hfirst, hlast⟩ := hΨ.2 hne
    constructor
    · exact hfirst.trans (by exact_mod_cast hMM)
    · have hm : -(M : ℤ) ≤ -(Ms Ψ : ℤ) := neg_le_neg (Int.ofNat_le.mpr hMM)
      exact hm.trans hlast

omit [MeasurableSpace F]
  [@BorelSpace F (⟨⟩ : LocalFieldData F).topology _] in
/-- Moving the inverse block rotation through a diagonal permutes its entries. -/
theorem blockRotation_inv_mul_diagonal (d : Fin (t + 1) → Fˣ) :
    (blockRotation h F)⁻¹ * Iwasawa.diagonalUnits d =
      Iwasawa.diagonalUnits
        (fun j => d ((succBlockShape m h).reversePermutation.symm j)) *
      (blockRotation h F)⁻¹ := by
  have hc : (blockRotation h F)⁻¹ * Iwasawa.diagonalUnits d *
      blockRotation h F = Iwasawa.diagonalUnits
        (fun j => d ((succBlockShape m h).reversePermutation.symm j)) := by
    apply Units.ext
    ext i j
    rw [blockRotation_inv_conj_apply]
    change (Matrix.diagonal fun i => (d i : F))
        ((succBlockShape m h).reversePermutation.symm i)
        ((succBlockShape m h).reversePermutation.symm j) =
      (Matrix.diagonal fun i => (d ((succBlockShape m h).reversePermutation.symm i) : F)) i j
    simp only [Matrix.diagonal_apply,
      (succBlockShape m h).reversePermutation.symm.injective.eq_iff]
  calc
    _ = ((blockRotation h F)⁻¹ * Iwasawa.diagonalUnits d *
        blockRotation h F) * (blockRotation h F)⁻¹ := by group
    _ = _ := by rw [hc]

/-- The compact-uniform row-factor bound in the representatives transported
from the standard quotient. -/
theorem exists_partialSection_rotated_diagonal_compact_bounds
    (hsd : letI := (⟨⟩ : LocalFieldData F).fieldT2
      letI : NonarchimedeanRing F := by
        convert! ValuativeRel.nonarchimedeanRing F
        exact Valuation.toTopologicalSpace_eq _
      IsSelfDual ψ μ)
    (K : Set (GeneralLinear (t + 1) F))
    (hK : IsCompact K) :
    ∃ (C : ℝ) (M : ℕ), 0 < C ∧
      ∀ (d : Fin (t + 1) → Fˣ) (k : GeneralLinear (t + 1) F), k ∈ K →
      ‖partialSection h ψ μ Φ
        ((blockRotation h F)⁻¹ * Iwasawa.diagonalUnits d * k)‖ ≤
        C * ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
          (∑ j, ((⟨⟩ : LocalFieldData F).ord (d j : F)).natAbs) ∧
      (partialSection h ψ μ Φ
        ((blockRotation h F)⁻¹ * Iwasawa.diagonalUnits d * k) ≠ 0 →
        (⟨⟩ : LocalFieldData F).ord
          (d ((succBlockShape m h).reversePermutation.symm
            ((succBlockShape m h).index 0 0)) : F) ≤ M ∧
        -(M : ℤ) ≤ (⟨⟩ : LocalFieldData F).ord
          (d ((succBlockShape m h).reversePermutation.symm
            ((succBlockShape m h).index 1 (Fin.last (m 1)))) : F)) := by
  let K' := (fun k : GeneralLinear (t + 1) F => (blockRotation h F)⁻¹ * k) '' K
  have hK' : IsCompact K' := hK.image (continuous_const.mul continuous_id)
  obtain ⟨C, M, hC, hb⟩ := exists_partialSection_diagonal_compact_bounds h ψ μ Φ hsd K' hK'
  refine ⟨C, M, hC, fun d k hk => ?_⟩
  have heq : (blockRotation h F)⁻¹ * Iwasawa.diagonalUnits d * k =
      Iwasawa.diagonalUnits (fun j => d ((succBlockShape m h).reversePermutation.symm j)) *
        ((blockRotation h F)⁻¹ * k) := by
    rw [blockRotation_inv_mul_diagonal, mul_assoc]
  have hsum := Equiv.sum_comp (succBlockShape m h).reversePermutation.symm
    (fun j => ((⟨⟩ : LocalFieldData F).ord (d j : F)).natAbs)
  rw [heq]
  simpa only [hsum] using hb
    (fun j => d ((succBlockShape m h).reversePermutation.symm j))
    ((blockRotation h F)⁻¹ * k) ⟨k, hk, rfl⟩

/-- Specialization to the canonical uniformizer torus, with endpoint cutoffs
at the adjacent standard coordinates on either side of the block cut. -/
theorem exists_partialSection_rotated_torus_compact_bounds
    (hsd : letI := (⟨⟩ : LocalFieldData F).fieldT2
      letI : NonarchimedeanRing F := by
        convert! ValuativeRel.nonarchimedeanRing F
        exact Valuation.toTopologicalSpace_eq _
      IsSelfDual ψ μ)
    (K : Set (GeneralLinear (t + 1) F))
    (hK : IsCompact K)
    (j : Fin t) (hj : (j : ℕ) = m 1) :
    ∃ (C : ℝ) (M : ℕ), 0 < C ∧
      ∀ (lam : Fin (t + 1) → ℤ) (k : GeneralLinear (t + 1) F), k ∈ K →
      ‖partialSection h ψ μ Φ ((blockRotation h F)⁻¹ *
        Iwasawa.torus (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F))
          lam * k)‖ ≤ C * ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
          (∑ i, (lam i).natAbs) ∧
      (partialSection h ψ μ Φ ((blockRotation h F)⁻¹ *
        Iwasawa.torus (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F))
          lam * k) ≠ 0 → lam j.succ ≤ M ∧ -(M : ℤ) ≤ lam j.castSucc) := by
  let T := (⟨⟩ : LocalFieldData F)
  have hfirst : (succBlockShape m h).reversePermutation.symm
      ((succBlockShape m h).index 0 0) = j.succ := by
    apply Fin.ext
    rw [val_reversePermutation_symm_index_zero]
    simp only [Fin.val_succ, Fin.val_zero]
    omega
  have hlast : (succBlockShape m h).reversePermutation.symm
      ((succBlockShape m h).index 1 (Fin.last (m 1))) = j.castSucc := by
    apply Fin.ext
    rw [val_reversePermutation_symm_index_one]
    simp only [Fin.val_last, Fin.val_castSucc]
    exact hj.symm
  obtain ⟨C, M, hC, hb⟩ := exists_partialSection_rotated_diagonal_compact_bounds h ψ μ Φ hsd K hK
  refine ⟨C, M, hC, fun lam k hk => ?_⟩
  have hord (i : Fin (t + 1)) :
      (⟨⟩ : LocalFieldData F).ord
        ((Langlands.LocalFactor.LocalAbelian.uniformizerUnit T ^ lam i : Fˣ) : F) =
      lam i := by
    change T.ord _ = _
    simp only [Units.val_zpow_eq_zpow_val,
      Langlands.LocalFactor.LocalAbelian.uniformizerUnit_coe, T.ord_zpow, T.ord_uniformizer, mul_one]
  simpa only [Iwasawa.torus, hord, hfirst, hlast] using
    hb (fun i => Langlands.LocalFactor.LocalAbelian.uniformizerUnit T ^ lam i) k hk

end Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding
