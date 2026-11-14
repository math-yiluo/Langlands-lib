import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedOrbitFourier
import Langlands.AllField.Representation.RankinSelberg.AnalyticBridge
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierExchange
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierInvariance
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFramedIntegrability
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUnipotentIota
import Langlands.AllField.Representation.RankinSelberg.UnequalRankFiniteExpansionProof
/-! Actual signed inverse-character orbit Fourier exchange on unipotent times matrices. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis
open Langlands.RankinSelberg.CompactWhittakerSynthesis hiding firstColumnFrame_mem_range_of_mem_box instValuativeRelCarrier_1 integrable_signedUnipotentMatrixFourierDualKernel integrable_signedUnipotentMatrixFourierOriginalKernel integral_signedUnipotentMatrixFourierKernel_fixed signedOrbitBorelSpace signedOrbitGLSecondCountable signedOrbitLocalField signedOrbitMeasurableSpace signedOrbitNBorelSpace signedOrbitNLocallyCompact signedOrbitNMeasurableSpace signedOrbitNSecondCountable signedOrbitSecondCountable signedOrbitT2 signedOrbitTopology signedOrbitTotallyDisconnected signedOrbitValuativeRel signedUnipotentMatrixFourier_exchange
open Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map exists_rankOneCutoff exists_rankOneEmbedding_support lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneModelValues_subset_whittakerRationalValues singleton_modulus_real unequalRankFiniteExpansion zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory MeasureTheory.Measure _root_.Topology
open Langlands.HarmonicAnalysis hiding PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularFourierIntegral_exchange_left padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest
open Langlands.AllField.Whittaker

universe uK uF

section General



end General

section CanonicalPadic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance signedOrbitT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance signedOrbitTotallyDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance signedOrbitSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance signedOrbitMeasurableSpace : MeasurableSpace F := borel _
local instance signedOrbitBorelSpace : BorelSpace F := ⟨rfl⟩
local instance signedOrbitGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology (n + 1)
local instance signedOrbitNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).upperUnipotentLocallyCompactSpace (n + 1)
local instance signedOrbitNSecondCountable (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance signedOrbitNMeasurableSpace (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance signedOrbitNBorelSpace (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩

private theorem continuous_standardPhase (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    Continuous (fun u : upperUnipotent (n + 1) F =>
      (standardCharacter ψ n u : ℂ)) :=
  Units.continuous_val.comp (standardCharacterContinuous ψ n).continuous

/-- Genuine joint convergence of the Fourier side follows from reflection and
the actual positive-level box frame; the transformed first test may meet singular matrices. -/
theorem integrable_signedUnipotentMatrixFourierDualKernel
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (A q : ℤ) {a : ℕ} (ha : 0 < a)
    (hΨ : tsupport (Ψ : _ → ℂ) ⊆ Langlands.AllField.RankinSelberg.RankOneBox.box F A q a) :
    Integrable (signedUnipotentMatrixFourierDualKernel ψ ν n Φ Ψ)
      ((unipotentHaar F n).prod (rectangularMeasure ν (n + 1) (n + 1))) := by
  let Φhat := rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Φ
  let Φhatw := rectangularLeftRightTranslate (rankOneSignedWeyl n)⁻¹ 1 Φhat
  have hi := integrable_weighted_framed_matrix_product (n + 1)
    (upperUnipotent (n + 1) F) UpperUnipotent.isClosed
    (fun u => unipotent_det u) (firstColumnFrame n) (continuous_firstColumnFrame n)
    (firstColumnFrame_mul n) (unipotentHaar F n)
    (rectangularMeasure ν (n + 1) (n + 1)) Φhatw Ψ
    (fun X hX => firstColumnFrame_mem_range_of_mem_box F n A q ha X (hΨ hX))
    (fun u => (inverseStandardCharacter ψ n u : ℂ)) (fun _ => 1)
    (Units.continuous_val.comp ((standardCharacterContinuous ψ n).continuous.inv)) continuous_const
  have hp := measurePreserving_signedReflectedUnipotent_prod n
    (unipotentHaar F n) (rectangularMeasure ν (n + 1) (n + 1))
  have h := hp.integrable_comp_of_integrable hi
  unfold signedUnipotentMatrixFourierDualKernel
  simpa only [Function.comp_def, Φhatw, rectangularLeftRightTranslate_apply,
    Units.val_one, Matrix.mul_one, inverseStandardCharacter_signedReflected, mul_one,
    ← Matrix.mul_assoc, ← Units.val_mul, signedWeyl_inv_mul_signedReflected,
    Φhat, rectangularFourierEquiv_apply] using h

/-- Genuine joint convergence of the original side, using only invertible
support of the fixed lift and the same supplied Haar measures. -/
theorem integrable_signedUnipotentMatrixFourierOriginalKernel
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (hΦ : tsupport (Φ : _ → ℂ) ⊆
      Set.range (Units.val : Langlands.GeneralLinear (n + 1) F →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F)) :
    Integrable (signedUnipotentMatrixFourierOriginalKernel ψ ν n Φ Ψ)
      ((unipotentHaar F n).prod (rectangularMeasure ν (n + 1) (n + 1))) := by
  let Ψhat := rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd Ψ
  let Ψhatw := rectangularLeftRightTranslate (rankOneSignedWeyl n) 1 Ψhat
  have hi := integrable_weighted_framed_matrix_product (n + 1)
    (upperUnipotent (n + 1) F) UpperUnipotent.isClosed
    (fun u => unipotent_det u) id continuous_id (fun _ _ => rfl)
    (unipotentHaar F n) (rectangularMeasure ν (n + 1) (n + 1)) Ψhatw Φ
    (fun X hX => hΦ hX)
    (fun u => (standardCharacter ψ n u : ℂ)) (fun _ => 1)
    (continuous_standardPhase F ψ n) continuous_const
  have hp := (Measure.measurePreserving_inv (unipotentHaar F n)).prod
    (MeasurePreserving.id (rectangularMeasure ν (n + 1) (n + 1)))
  have h := hp.integrable_comp_of_integrable hi
  unfold signedUnipotentMatrixFourierOriginalKernel
  simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq, Ψhatw,
    rectangularLeftRightTranslate_apply,
    Units.val_one, Matrix.mul_one, map_inv, Subgroup.coe_inv, mul_one, one_mul,
    Ψhat, rectangularFourierEquiv_apply,
    Units.val_mul, Matrix.mul_assoc, inverseStandardCharacter,
    MonoidHom.inv_apply, mul_assoc, mul_left_comm, mul_comm] using h

/-- Fixed-unipotent bilinear Fourier exchange in exactly the two kernel arguments. -/
theorem integral_signedUnipotentMatrixFourierKernel_fixed
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (u : upperUnipotent (n + 1) F) :
    (∫ X, signedUnipotentMatrixFourierDualKernel ψ ν n Φ Ψ (u, X)
      ∂rectangularMeasure ν (n + 1) (n + 1)) =
    ∫ X, signedUnipotentMatrixFourierOriginalKernel ψ ν n Φ Ψ (u, X)
      ∂rectangularMeasure ν (n + 1) (n + 1) := by
  let T := (⟨⟩ : LocalFieldData F)
  let B := inverseTranspose (n + 1) F u.val * (rankOneSignedWeyl n)⁻¹
  have hu : T.determinantNorm (n + 1) u.val = 1 := by
    apply Units.ext
    apply NNReal.coe_injective
    simp only [T.determinantNorm_coe, Units.val_one, NNReal.coe_one]
    change T.normalizedAbs u.val.val.det = 1
    rw [unipotent_det, T.normalizedAbs_one]
  have hB : T.determinantNorm (n + 1) B = 1 := by
    have hT : T.determinantNorm (n + 1) (rankOneWeylAlternating (K := F) n) = 1 := by
      apply T.determinantNorm_eq_one_of_pow_eq_one _ (by decide : 2 ≠ 0)
      simpa only [pow_two] using rankOneWeylAlternating_mul_self (K := F) n
    simp only [B, map_mul, T.determinantNorm_inverseTranspose, hu, inv_one,
      rankOneSignedWeyl, map_inv, T.determinantNorm_weylLong, hT, one_mul]
  have he := (padicRectangularFourierIntegral_exchange_left F T (n + 1) (n + 1)
    ψ ν 1 B (map_one _) hB Φ Ψ).2.2
  have harg : inverseTranspose (n + 1) F (1 * B⁻¹) =
      rankOneSignedWeyl n * u.val⁻¹ := by
    simp only [one_mul, B, map_inv, map_mul, rankOneSignedWeyl,
      inverseTranspose_weylLong, inverseTranspose_rankOneWeylAlternating,
      inverseTranspose_involutive, mul_inv_rev, inv_inv]
  simp only [Units.val_one, Matrix.one_mul, harg] at he
  simp only [signedUnipotentMatrixFourierDualKernel, signedUnipotentMatrixFourierOriginalKernel,
    mul_assoc, integral_const_mul]
  exact congrArg (fun c : ℂ => (inverseStandardCharacter ψ n u : ℂ) * c) he

/-- The actual signed Weyl orbit Fourier exchange, with both joint
integrabilities proved before Fubini and the unchanged supplied self-dual measure. -/
theorem signedUnipotentMatrixFourier_exchange
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (n : ℕ)
    (Φ Ψ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (hΦ : tsupport (Φ : _ → ℂ) ⊆
      Set.range (Units.val : Langlands.GeneralLinear (n + 1) F →
        Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (A q : ℤ) {a : ℕ} (ha : 0 < a)
    (hΨ : tsupport (Ψ : _ → ℂ) ⊆ Langlands.AllField.RankinSelberg.RankOneBox.box F A q a) :
    Integrable (signedUnipotentMatrixFourierDualKernel ψ ν n Φ Ψ)
      ((unipotentHaar F n).prod (rectangularMeasure ν (n + 1) (n + 1))) ∧
    Integrable (signedUnipotentMatrixFourierOriginalKernel ψ ν n Φ Ψ)
      ((unipotentHaar F n).prod (rectangularMeasure ν (n + 1) (n + 1))) ∧
    (∫ z, signedUnipotentMatrixFourierDualKernel ψ ν n Φ Ψ z
      ∂(unipotentHaar F n).prod (rectangularMeasure ν (n + 1) (n + 1))) =
    ∫ z, signedUnipotentMatrixFourierOriginalKernel ψ ν n Φ Ψ z
      ∂(unipotentHaar F n).prod (rectangularMeasure ν (n + 1) (n + 1)) := by
  have hd := integrable_signedUnipotentMatrixFourierDualKernel F ψ ν hsd n Φ Ψ A q ha hΨ
  have ho := integrable_signedUnipotentMatrixFourierOriginalKernel F ψ ν hsd n Φ Ψ hΦ
  refine ⟨hd, ho, ?_⟩
  rw [integral_prod _ hd, integral_prod _ ho]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (integral_signedUnipotentMatrixFourierKernel_fixed F ψ ν n Φ Ψ)

end CanonicalPadic

end Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis
