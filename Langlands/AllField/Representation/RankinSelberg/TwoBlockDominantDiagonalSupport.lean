import Langlands.Representation.RankinSelberg.TwoBlockDominantDiagonalSupport
import Langlands.AllField.Representation.RankinSelberg.CorankCommonCompactSupport
/-! # Compact support of diagonal test restrictions on determinant slices -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg.TwoBlockDominantFirstBlock hiding diagonalSupportGLTopological diagonalSupportT2 diagonalSupportTopology diagonalWhittaker_slice_hasCompactSupport
open Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankSliceSupportStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable whittakerRowSliceCompactSupport zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.QuotientIntegration

universe uF uV

section Algebra

variable {K : Type uF} [Field K] [TopologicalSpace K]

/-- Continuity of the actual inclusion checks the value and inverse matrices. -/
private theorem continuous_diagonalInclusion (n d : ℕ) :
    Continuous (appendIdentity (F := K) n d) := by
  induction d with
  | zero => exact continuous_id
  | succ d ih => exact (GeneralLinear.rankInclusionContinuous 1).continuous.comp ih

end Algebra

section Padic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance diagonalSupportT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance diagonalSupportGLTopological (a : ℕ) : IsTopologicalGroup (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup a

/-- The norm of the diagonal restriction of every smooth coefficient has compact
support on every fixed determinant slice. No functional nonvanishing, finite
length, irreducibility or analytic estimate is required. -/
theorem diagonalWhittaker_slice_hasCompactSupport (n d : ℕ)
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (n + (d + 1) + 1) F) V)
    (hπ : IsSmooth π) (lambda : glFunctionals ψ (n + (d + 1)) π)
    (W : (coefficientModel π lambda).toSubmodule) (a : ℤ) :
    HasCompactSupport ((determinantSlice (⟨⟩ : LocalFieldData F) n a).indicator
      (whittakerNorm ψ (diagonalWhittaker ψ (d + 1) W.val))) := by
  induction d with
  | zero =>
      obtain ⟨K, hK⟩ := model_isSmooth π hπ lambda W
      have hfix : ∀ (z : ℂ) g (k : K.toSubgroup), W.val.val (g * k) = W.val.val g := by
        intro z g k
        exact congrArg (fun f : (coefficientModel π lambda).toSubmodule => f.val.val g)
          (hK k)
      obtain ⟨C, hC, hsupport⟩ := Langlands.AllField.RankinSelberg.CommonLevel.corank_common_compact_support
        (⟨⟩ : LocalFieldData F) n ψ (fun _ : ℂ => W.val) K.toSubgroup K.isOpen hfix a
      let : T2Space (LeftUnipotentQuotient n F) :=
        leftQuotient_t2Space _ (UpperUnipotent.isClosed (R := F))
      apply hC.of_isClosed_subset isClosed_closure
      apply closure_minimal _ hC.isClosed
      intro q hq
      apply hsupport 0 (reciprocalWhittaker ψ (diagonalWhittaker ψ 1 W.val)) 0
      induction q using Quotient.inductionOn with
      | h g =>
          rw [Function.mem_support, Set.indicator_apply_ne_zero] at hq ⊢
          refine ⟨hq.1, ?_⟩
          have hn : W.val.val (rankInclusion 1 g) ≠ 0 := by
            have hz := hq.2
            change whittakerNorm ψ (diagonalWhittaker ψ 1 W.val) ⟦g⟧ ≠ 0 at hz
            rw [whittakerNorm_mk] at hz
            simpa only [diagonalWhittaker, appendIdentity, MonoidHom.comp_apply,
              MonoidHom.id_apply, norm_ne_zero_iff] using hz
          change W.val.val (rankInclusion 1 g) *
            (W.val.val (appendIdentity n 1 g))⁻¹ *
              determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
                (0 - (1 : ℂ) / 2) ≠ 0
          simpa only [appendIdentity, MonoidHom.comp_apply, MonoidHom.id_apply,
            mul_inv_cancel₀ hn, one_mul] using
              determinantWeight_ne_zero (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
                (0 - (1 : ℂ) / 2)
  | succ d ih =>
      obtain ⟨v, rfl⟩ := modelMap_surjective π lambda W
      let πsmall := π.comp (rankInclusion 1)
      let lsmall := diagonalFunctional ψ π lambda
      have hsmall : IsSmooth πsmall := by
        apply isSmooth_comp _ _ hπ
        simpa only [appendIdentity, MonoidHom.comp_id] using
          continuous_diagonalInclusion (K := F) (n + (d + 1)) 1
      exact ih πsmall hsmall lsmall (modelMap πsmall lsmall v)

end Padic

end Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
