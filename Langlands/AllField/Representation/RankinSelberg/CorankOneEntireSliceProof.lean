import Langlands.Representation.RankinSelberg.CorankOneEntireSliceProof
import Langlands.AllField.Representation.RankinSelberg.CorankCommonCompactSupport
import Langlands.AllField.Representation.RankinSelberg.CorankSliceFiniteEvaluation
/-!
# Entire dependence on corank determinant slices

The common right level first gives a common compact quotient support on each
fixed determinant slice. Smoothness of the fixed coefficient then gives a finite
orbit formula for the actual restricted integrals, independent of the parameter.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding CorankOneEntireSliceStatement EqualRankAnalyticStatement EqualRankSliceSupportStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement continuous_determinantOrder continuous_ord_units corankOneEntireSlice determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable whittakerRowSliceCompactSupport zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV

/-- Every corank determinant slice of a common-level pointwise entire family is
integrable and has an entire literal slice coefficient. -/
theorem corankOneEntireSlice : CorankOneEntireSliceStatement.{uF,uV} := by
  intro F _ _ _ _
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  intro ψ r
  let := borel (Langlands.GeneralLinear (r + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (r + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (r + 1) F)
  let : BorelSpace (upperUnipotent (r + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient r F)
  let : BorelSpace (LeftUnipotentQuotient r F) := ⟨rfl⟩
  intro _ ν hν V _ _ τ hτ ℓ Wprime U hK hU m
  obtain ⟨K, hKo, _, hKinv⟩ := hK
  obtain ⟨C, hC, hCs⟩ := Langlands.AllField.RankinSelberg.CommonLevel.corank_common_compact_support
    (⟨⟩ : LocalFieldData F) r ψ U K hKo hKinv m
  have := hν.regular
  exact Langlands.AllField.RankinSelberg.CommonLevel.corank_slice_of_common_support (⟨⟩ : LocalFieldData F) r
    ψ ν V τ hτ ℓ Wprime U K hKo hKinv hU m C hC (fun z => hCs z _ 0)

end Langlands.AllField.RankinSelberg
