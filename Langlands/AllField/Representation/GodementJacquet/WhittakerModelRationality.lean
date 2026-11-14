import Langlands.Representation.GodementJacquet.WhittakerModelRationality
import Langlands.AllField.Representation.GodementJacquet.WhittakerMatrixConvergence
import Langlands.AllField.Representation.GodementJacquet.WhittakerModelInclusion
import Langlands.AllField.Representation.RankinSelberg.ModelAsymptoticProof
/-!
# Whittaker integrals on the coefficient model

The functions of the coefficient model of a representation of Whittaker type
satisfy `IsWhittakerLike`, given the torus expansion of
`CoefficientTorusExpansion`. Hence their shifted full-matrix integrals converge
on a right half-plane and have rational continuations. This proves
`ModelWhittakerRationalityStatement` and `WhittakerModelComparisonStatement` from
`WhittakerTypeAsymptoticStatement` and `FiniteFunctionMellinStatement`. See the
paired Markdown.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet.WhittakerTorus
open Langlands.GodementJacquet.WhittakerTorus
open Langlands.AllField.GodementJacquet.WhittakerTorus
open Langlands.GodementJacquet hiding ModelWhittakerRationalityStatement WhittakerModelComparisonStatement whittakerModelComparison_of_rationality
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement FiniteFunctionMellinStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable unequalRankIwasawaSupport unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open scoped BigOperators

universe uF uV

namespace Padic
open Langlands.GodementJacquet.WhittakerTorus.Padic hiding HasTorusExpansion IsWhittakerLike borelModulus borelModulus_mul borelModulus_pos boxTest boxTest_apply_of_le continuous_borelModulus continuous_normalizedAbs_prod continuous_torusWeight enorm_torusWeight exists_slice_bound glModelFunction_isWhittakerLike glModel_shifted_of_converges initTail integralK integral_iwasawa integral_unipotent_matrixIntegrand isClopen_normBox isCompact_normBox isFiniteFunction_torusWeight isFiniteFunction_twistedCharacter iwasawaReductionBorelSpace iwasawaReductionLocalField iwasawaReductionMeasurableSpace iwasawaReductionTopology iwasawaReductionUnipotentBorelSpace iwasawaReductionUnipotentMeasurableSpace iwasawaReductionUnitsBorelSpace iwasawaReductionUnitsMeasurableSpace iwasawaReductionValuativeRel lintegral_iwasawa lintegral_torus_lt_top lintegral_unipotent_matrixIntegrand matrixConvergenceBorelSpace matrixConvergenceLocalField matrixConvergenceMeasurableSpace matrixConvergenceTopology matrixConvergenceUnipotentBorelSpace matrixConvergenceUnipotentMeasurableSpace matrixConvergenceUnitsBorelSpace matrixConvergenceUnitsMeasurableSpace matrixConvergenceValuativeRel matrixIntegrand_iwasawa matrixIntegrand_mul_right matrixRationalityBorelSpace matrixRationalityLocalField matrixRationalityMeasurableSpace matrixRationalityTopology matrixRationalityUnipotentBorelSpace matrixRationalityUnipotentMeasurableSpace matrixRationalityUnitsBorelSpace matrixRationalityUnitsMeasurableSpace matrixRationalityValuativeRel measurable_matrixIntegrand modelRationalityLocalField modelRationalityTopology modelRationalityValuativeRel modelWhittakerRationality normBox normalizedAbs_det_integralK normalizedAbs_prod_mul normalizedAbs_prod_pos normalizedAbs_units_pos ratios sliceBoundBorelSpace sliceBoundLocalField sliceBoundMeasurableSpace sliceBoundTopology sliceBoundUnipotentBorelSpace sliceBoundUnipotentMeasurableSpace sliceBoundValuativeRel sliceTest sliceTest_apply torusIntegrand torusIntegrand_tailProd torusMellin torusMellinLocalField torusMellinTopology torusMellinUnitsBorelSpace torusMellinUnitsMeasurableSpace torusMellinValuativeRel torusMonomial torusMonomial_nonneg torusWeight torusWeight_mul twistedCharacter whittakerModelComparison_of_asymptotics
open Langlands.AllField.GodementJacquet.WhittakerTorus.Padic
open Langlands.GodementJacquet.WhittakerTorus
open Langlands.AllField.GodementJacquet.WhittakerTorus
open Langlands.GodementJacquet hiding ModelWhittakerRationalityStatement WhittakerModelComparisonStatement whittakerModelComparison_of_rationality
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

variable {n : ℕ}

/-- The functions of the coefficient model of an admissible representation
with a torus expansion are Whittaker-like. -/
theorem glModelFunction_isWhittakerLike (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hσ : IsAdmissible σ) (hexp : CoefficientTorusExpansion (standardCharacter ψ n) σ)
    (ℓ : glFunctionals ψ n σ) (w : (glCoefficientModel ψ n σ ℓ).toSubmodule) :
    IsWhittakerLike F ψ (glModelFunction ψ n σ ℓ w) where
  continuous := glModelFunction_continuous ψ n σ hσ.1 ℓ w
  equivariant := glModelFunction_equivariance ψ n σ ℓ w
  smooth := by
    obtain ⟨L, hL⟩ := (Langlands.AllField.GodementJacquet.Padic.glModel_isAdmissible F ψ σ ℓ hσ).1 w
    refine ⟨L, fun g k hk => ?_⟩
    have hfix : glModelRepresentation ψ n σ ℓ k w = w := hL ⟨k, hk⟩
    rw [← glModelFunction_translate ψ n σ ℓ w k g, hfix]
  expansion := fun k => by
    obtain ⟨X, hX, hφ⟩ := hexp
    obtain ⟨φ, hφ'⟩ := hφ ℓ (glModelRepresentation ψ n σ ℓ k w)
    exact ⟨X, hX, φ, fun a => hφ' a⟩

/-- The shifted full-matrix integrals of a coefficient-model function converge on
a right half-plane and have a rational continuation in `q^(-s)`, given
`FiniteFunctionMellinStatement`, the torus expansion, and convergence of the
unshifted integrals on some right half-plane. -/
theorem glModel_shifted_of_converges (hFFM : FiniteFunctionMellinStatement.{uF})
    (ψ : UnitaryAdditiveCharacter F) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hσ : IsAdmissible σ) (hexp : CoefficientTorusExpansion (standardCharacter ψ n) σ)
    (ℓ : glFunctionals ψ n σ) (Φ : MatrixTestFunction n F)
    (w : (glCoefficientModel ψ n σ ℓ).toSubmodule)
    (hconv : ∃ c : ℝ, ∀ s : ℂ, c < s.re →
      Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ s (glModelFunction ψ n σ ℓ w)) :
    (∃ a : ℝ, ∀ s : ℂ, a < s.re →
      Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ (s + jpssShift n)
        (glModelFunction ψ n σ ℓ w)) ∧
    ∃ R : RationalFunctions,
      HasRationalContinuation (⟨⟩ : LocalFieldData F).residueCardinality
        (fun s => Langlands.AllField.GodementJacquet.Padic.matrixIntegral F Φ (s + jpssShift n)
          (glModelFunction ψ n σ ℓ w)) R := by
  obtain ⟨c, hc⟩ := hconv
  refine ⟨⟨c - (jpssShift n).re, fun s hs => hc _ (by rw [Complex.add_re]; linarith)⟩, ?_⟩
  exact (glModelFunction_isWhittakerLike F ψ σ hσ hexp ℓ w).hasRationalContinuation F hFFM Φ
    (jpssShift n) ⟨c, hc⟩

/-- `ModelWhittakerRationalityStatement` follows from
`WhittakerTypeAsymptoticStatement` and `FiniteFunctionMellinStatement`. -/
theorem modelWhittakerRationality (hWTA : WhittakerTypeAsymptoticStatement.{uF, uV})
    (hFFM : FiniteFunctionMellinStatement.{uF}) :
    Langlands.AllField.GodementJacquet.ModelWhittakerRationalityStatement.{uF, uV} := by
  intro F _ _ _ _ ψ n V _ _ σ hσ ℓ _ Φ w
  have hexp := modelAsymptoticTransfer hWTA F (⟨⟩ : LocalFieldData F) n V σ ψ
    (standardCharacter ψ n) (Or.inl rfl) hσ
  exact glModel_shifted_of_converges F hFFM ψ σ hσ.1 hexp ℓ Φ w
    ((glModelFunction_isWhittakerLike F ψ σ hσ.1 hexp ℓ w).matrixConverges F hFFM Φ)

/-- `WhittakerModelComparisonStatement` follows from
`WhittakerTypeAsymptoticStatement` and `FiniteFunctionMellinStatement`. -/
theorem whittakerModelComparison_of_asymptotics
    (hWTA : WhittakerTypeAsymptoticStatement.{uF, uV})
    (hFFM : FiniteFunctionMellinStatement.{uF}) :
    Langlands.AllField.GodementJacquet.WhittakerModelComparisonStatement.{uF, uV} :=
  Langlands.AllField.GodementJacquet.whittakerModelComparison_of_rationality (modelWhittakerRationality hWTA hFFM)

end Padic

end Langlands.AllField.GodementJacquet.WhittakerTorus
