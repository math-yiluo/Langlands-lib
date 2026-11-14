import Langlands.Representation.RankinSelberg.CorankCommonCompactSupport
import Langlands.AllField.Representation.RankinSelberg.CommonLevelRootSupport
import Langlands.AllField.Representation.RankinSelberg.WhittakerRowSliceCompactSupportProof
/-! # Common compact support of corank determinant slices -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.CommonLevel
open Langlands.RankinSelberg.CommonLevel hiding corank_common_compact_support corank_diagonal_upper diagonalAnnulusImage diagonalAnnulusImage_isCompact exists_uniform_lattice root_bound
open Langlands.AllField.RankinSelberg.CommonLevel
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankSliceSupportStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable whittakerRowSliceCompactSupport zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.QuotientIntegration

universe uF

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- The appended final coordinate is one, so bounds on all roots of the larger
group bound every diagonal entry of the smaller group. -/
theorem corank_diagonal_upper (r : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (W : WhittakerFunctions ψ (r + 1)) {R : ℝ}, 0 < R →
      (∀ (b : Fin (r + 1 + 1) → Fˣ)
        (κ : Langlands.GeneralLinear (r + 1 + 1) F),
        κ ∈ Conductor.integralSubgroup (ValuativeRel.valuation F).integer (r + 1) →
        W.val (Iwasawa.diagonalUnits b * κ) ≠ 0 →
        ∀ i : Fin (r + 1),
          T.normalizedAbs ((b i.castSucc / b i.succ : Fˣ) : F) ≤ R) →
      ∀ (a : Fin (r + 1) → Fˣ)
        (κ : Langlands.GeneralLinear (r + 1) F),
        κ ∈ Conductor.integralSubgroup (ValuativeRel.valuation F).integer r →
        W.val (rankInclusion 1 (Iwasawa.diagonalUnits a * κ)) ≠ 0 →
        ∀ i, T.normalizedAbs ((a i : Fˣ) : F) ≤
          max R 1 ^ (r + 1) := by
  let := T.topology
  let := T.valuativeRel
  intro ψ W R hR hroot a κ hκ hnonzero
  let b : Fin (r + 1 + 1) → Fˣ := Fin.snoc a 1
  have hκ' : rankInclusion 1 κ ∈
      Conductor.integralSubgroup (ValuativeRel.valuation F).integer (r + 1) :=
    Iwasawa.rankInclusion_mem _ hκ
  have hW : W.val (Iwasawa.diagonalUnits b * rankInclusion 1 κ) ≠ 0 := by
    simpa only [map_mul, rankInclusion_diagonalUnits_snoc] using hnonzero
  have hratio := hroot b (rankInclusion 1 κ) hκ' hW
  have hbound : ∀ i : Fin (r + 1 + 1),
      T.normalizedAbs ((b i : Fˣ) : F) ≤ R ^ (r + 1 - i.val) := by
    intro i
    induction i using Fin.reverseInduction with
    | last => simp [b, T.normalizedAbs_one]
    | cast i ih =>
      have hsplit : ((b i.castSucc : Fˣ) : F) =
          ((b i.castSucc / b i.succ : Fˣ) : F) *
            ((b i.succ : Fˣ) : F) := by
        rw [← Units.val_mul, div_mul_cancel]
      have hexp : r + 1 - i.castSucc.val = (r + 1 - i.succ.val) + 1 := by
        rw [Fin.val_castSucc, Fin.val_succ]
        omega
      rw [hsplit, T.normalizedAbs_mul, hexp, pow_succ']
      exact mul_le_mul (hratio i) ih (T.normalizedAbs_nonneg _) hR.le
  intro i
  calc T.normalizedAbs ((a i : Fˣ) : F)
      ≤ R ^ (r + 1 - i.val) := by simpa [b] using hbound i.castSucc
    _ ≤ max R 1 ^ (r + 1 - i.val) :=
      pow_le_pow_left₀ hR.le (le_max_left _ _) _
    _ ≤ max R 1 ^ (r + 1) :=
      pow_le_pow_right₀ (le_max_right _ _) (Nat.sub_le _ _)

/-- A concrete compact container made from diagonal annuli and the integral
Iwasawa factor, mapped into the actual left-unipotent quotient. -/
def diagonalAnnulusImage (r : ℕ) (c M : ℝ) :
    Set (LeftUnipotentQuotient r F) :=
  letI := T.valuativeRel
  (fun x : (Fin (r + 1) → Fˣ) × Langlands.GeneralLinear (r + 1) F =>
    leftQuotientMap (upperUnipotent (r + 1) F) (Iwasawa.diagonalUnits x.1 * x.2)) ''
    ((Set.univ.pi fun _ =>
      {a : Fˣ | c ≤ T.normalizedAbs (a : F) ∧
        T.normalizedAbs (a : F) ≤ M}) ×ˢ
      (Conductor.integralSubgroup (ValuativeRel.valuation F).integer r :
        Set (Langlands.GeneralLinear (r + 1) F)))

theorem diagonalAnnulusImage_isCompact (r : ℕ) {c M : ℝ} (hc : 0 < c) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    IsCompact (diagonalAnnulusImage T r c M) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hA : IsCompact (Set.univ.pi fun _ : Fin (r + 1) =>
      {a : Fˣ | c ≤ T.normalizedAbs (a : F) ∧
        T.normalizedAbs (a : F) ≤ M}) :=
    isCompact_univ_pi fun _ => isCompact_normalizedAbs_annulus_units T hc
  have hK : IsCompact (Conductor.integralSubgroup (ValuativeRel.valuation F).integer r :
      Set (Langlands.GeneralLinear (r + 1) F)) := by
    rw [← Conductor.levelSubgroup_zero]
    exact Conductor.isCompact_levelOpenSubgroup F r 0
  apply (hA.prod hK).image
  exact (leftQuotient_isOpenQuotientMap _).continuous.comp
    (((GeneralLinear.continuous_diagonalUnits (r + 1)).comp continuous_fst).mul continuous_snd)

/-- One compact subset contains every slice-restricted support, uniformly over
the parameter, the inverse-character function and the spectral variable. -/
theorem corank_common_compact_support (r : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (U : ℂ → WhittakerFunctions ψ (r + 1))
      (K : Subgroup (Langlands.GeneralLinear (r + 1 + 1) F)),
      IsOpen (K : Set (Langlands.GeneralLinear (r + 1 + 1) F)) →
      (∀ z g (k : K), (U z).val (g * k) = (U z).val g) →
      ∀ m : ℤ, ∃ C : Set (LeftUnipotentQuotient r F), IsCompact C ∧
        ∀ z (W' : InverseWhittakerFunctions ψ r) s,
          Function.support ((determinantSlice T r m).indicator
            (corankOneIntegrand ψ (normalizedAbsoluteValue T) (U z) W' s)) ⊆ C := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ U K hK hU m
  obtain ⟨R, hR, hroot⟩ := root_bound F T (r + 1) ψ U K hK hU
  let M : ℝ := max R 1 ^ (r + 1)
  have hM1 : 1 ≤ M := one_le_pow₀ (le_max_right _ _)
  let c : ℝ := (T.residueCardinality : ℝ) ^ (-m) / M ^ r
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  have hc : 0 < c :=
    div_pos (zpow_pos (zero_lt_one.trans hq) _) (pow_pos (zero_lt_one.trans_le hM1) _)
  refine ⟨diagonalAnnulusImage T r c M, diagonalAnnulusImage_isCompact T r hc, ?_⟩
  intro z W' s q hsupport
  induction q using Quotient.inductionOn with
  | h g =>
    rw [Function.mem_support, Set.indicator_apply_ne_zero] at hsupport
    obtain ⟨hslice, hnonzero⟩ := hsupport
    rw [mk_mem_determinantSlice_iff_normalizedAbs] at hslice
    rw [Function.mem_support, corankOneIntegrand_mk] at hnonzero
    have hW : (U z).val (rankInclusion 1 g) ≠ 0 := by
      intro h
      exact hnonzero (by rw [h, zero_mul, zero_mul])
    obtain ⟨u, hu, a, κ, hκ, rfl⟩ :=
      exists_unipotent_diagonal_integral (ValuativeRel.valuation F) g
    have hWD : (U z).val (rankInclusion 1 (Iwasawa.diagonalUnits a * κ)) ≠ 0 := by
      intro h
      apply hW
      rw [map_mul]
      change (U z).val ((corankOneUnipotent ⟨u, hu⟩).val *
        rankInclusion 1 (Iwasawa.diagonalUnits a * κ)) = 0
      rw [(U z).property, h, mul_zero]
    have hupper : ∀ i, T.normalizedAbs ((a i : Fˣ) : F) ≤ M :=
      corank_diagonal_upper T r ψ (U z) hR (hroot z) a κ hκ hWD
    have hdet : (GeneralLinear.determinant (u * (Iwasawa.diagonalUnits a * κ)) :
        F) = (∏ i, ((a i : Fˣ) : F)) * Matrix.det κ.val := by
      rw [determinant_unipotent_mul ⟨u, hu⟩]
      change Matrix.det ((Iwasawa.diagonalUnits a).val * κ.val) = _
      rw [Matrix.det_mul, Iwasawa.diagonalUnits_val, Matrix.det_diagonal]
    have hprod : T.normalizedAbs (∏ i, ((a i : Fˣ) : F)) =
        ∏ i, T.normalizedAbs ((a i : Fˣ) : F) := by
      rw [← normalizedAbsoluteValue_apply, map_prod]
      rfl
    have hall : ∏ i, T.normalizedAbs ((a i : Fˣ) : F) =
        (T.residueCardinality : ℝ) ^ (-m) := by
      rw [← hslice, hdet, T.normalizedAbs_mul, hprod,
        normalizedAbs_det_of_mem_integralSubgroup T hκ, mul_one]
    have hlower : ∀ i, c ≤ T.normalizedAbs ((a i : Fˣ) : F) := by
      intro i
      have herase : ∏ j ∈ Finset.univ.erase i, T.normalizedAbs ((a j : Fˣ) : F)
          ≤ M ^ r := by
        calc ∏ j ∈ Finset.univ.erase i, T.normalizedAbs ((a j : Fˣ) : F)
            ≤ ∏ _j ∈ Finset.univ.erase i, M :=
              Finset.prod_le_prod₀ (fun j _ => T.normalizedAbs_nonneg _) fun j _ => hupper j
          _ = M ^ r := by
            rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
              Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
      rw [show c = (T.residueCardinality : ℝ) ^ (-m) / M ^ r from rfl,
        div_le_iff₀ (pow_pos (zero_lt_one.trans_le hM1) _), ← hall,
        ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      exact mul_le_mul_of_nonneg_left herase (T.normalizedAbs_nonneg _)
    refine ⟨(a, κ), ⟨fun i _ => ⟨hlower i, hupper i⟩, hκ⟩, ?_⟩
    apply Quotient.sound
    change QuotientGroup.rightRel _ (Iwasawa.diagonalUnits a * κ)
      (u * (Iwasawa.diagonalUnits a * κ))
    rw [QuotientGroup.rightRel_apply, mul_inv_cancel_right]
    exact hu

end Langlands.AllField.RankinSelberg.CommonLevel
