import Langlands.Representation.GodementJacquet.RegularMatrixZetaOperator
import Langlands.AllField.HarmonicAnalysis.PadicLatticeGeometryProof
import Langlands.AllField.Representation.GodementJacquet.CompactMatrixLaurent
import Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement
/-! # Actual zeta operators for regular matrix tests -/

noncomputable section

namespace Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet.Padic hiding MatrixConverges compactMatrixLaurentBorelSpace compactMatrixLaurentLocalField compactMatrixLaurentMeasurableSpace compactMatrixLaurentTopology compactMatrixLaurentValuativeRel determinantWeight_locallyConstant determinantWeight_shift_spectral exists_laurent_integral_of_hasCompactSupport exists_laurent_matrixIntegral_of_hasCompactSupport instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instTopologicalSpaceCarrier instValuativeRelCarrier jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues regularMatrixZetaGLBorel regularMatrixZetaGLMeasurable regularMatrixZetaLocalField regularMatrixZetaOperator regularMatrixZetaOperator_dual regularMatrixZetaTopology regularMatrixZetaValuation weightedRegularMatrixTest weightedRegularMatrixTest_apply whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding MatrixConverges jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicLatticeGeometry padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance regularMatrixZetaGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance regularMatrixZetaGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {n : ℕ}

/-- The actual determinant weight is locally constant at every complex exponent. -/
theorem determinantWeight_locallyConstant (s : ℂ) :
    IsLocallyConstant (fun g : GeneralLinear (n + 1) F =>
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g s) := by
  simp_rw [normalizedDeterminantWeight_eq_spectralPoint_zpow]
  exact ((IsLocallyConstant.iff_continuous _).mpr
    ((continuous_ord_units (⟨⟩ : LocalFieldData F)).comp
      ((⟨⟩ : LocalFieldData F).generalLinearDeterminant (n + 1)).continuous)).comp
        (fun m : ℤ => spectralPoint (⟨⟩ : LocalFieldData F).residueCardinality s ^ m)

/-- Restrict a regular full-matrix test to GL and multiply by the actual
determinant weight, preserving compact support and local constancy. -/
def weightedRegularMatrixTest (s : ℂ) :
    regularMatrixTests (K := F) (n + 1) →ₗ[ℂ]
      SchwartzBruhat (GeneralLinear (n + 1) F) where
  toFun Φ :=
    ⟨fun g => Φ.val g.val *
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g s,
      ((regularMatrixTestRestriction (n + 1) Φ).locallyConstant).mul
        (determinantWeight_locallyConstant F s),
      (hasCompactSupport_restrict_of_mem_regularMatrixTests (n + 1) Φ.property).mul_right⟩
  map_add' Φ Ψ := by
    apply Hecke.TestFunction.ext
    intro g
    exact add_mul _ _ _
  map_smul' c Φ := by
    apply Hecke.TestFunction.ext
    intro g
    exact mul_assoc c _ _

@[simp] theorem weightedRegularMatrixTest_apply (s : ℂ)
    (Φ : regularMatrixTests (K := F) (n + 1))
    (g : GeneralLinear (n + 1) F) :
    weightedRegularMatrixTest F s Φ g =
      Φ.val g.val *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g s := rfl

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The actual compact integral operator for a regular matrix test, constructed
without any topology or completeness on the representation carrier. -/
def regularMatrixZetaOperator
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
    (hρ : IsSmooth ρ) (s : ℂ) :
    regularMatrixTests (K := F) (n + 1) →ₗ[ℂ] Module.End ℂ V :=
  (Hecke.integratedAction (generalLinearHaar F n) ρ hρ).comp
    (weightedRegularMatrixTest F s)

/-- Every algebraic functional evaluates the operator as the actual matrix
integral, for the shared normalized group Haar measure. -/
theorem regularMatrixZetaOperator_dual
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
    (hρ : IsSmooth ρ) (s : ℂ)
    (Φ : regularMatrixTests (K := F) (n + 1))
    (v : V) (ℓ : Module.Dual ℂ V) :
    ℓ (regularMatrixZetaOperator F ρ hρ s Φ v) =
      matrixIntegral F Φ.val s (fun g => ℓ (ρ g v)) := by
  rw [regularMatrixZetaOperator, LinearMap.comp_apply, Hecke.integratedAction_dual]
  apply integral_congr_ae
  filter_upwards [] with g
  simp only [weightedRegularMatrixTest_apply, GodementJacquet.matrixIntegrand]
  ring

end Langlands.AllField.GodementJacquet.Padic
