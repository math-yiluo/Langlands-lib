import Langlands.Representation.RankinSelberg.AdjacentRankDualEntireCoefficientFamily
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankEntireCoefficientSpecialization
/-! Entire determinant-slice coefficients for the actual Weyl-translated dual family. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding HasCommonCompactOpenRightLevel adjacentRankDualCoefficientFamily adjacentRankDualCoefficientFamily_integrable_entire adjacentRankDualWhittakerFamily adjacentRankDualWhittakerFamily_level_entire clearingKernelTopology corankCoefficientFamily corankCoefficientFamily_integrable_entire dualEntireGroupBorel dualEntireGroupMeasurable dualEntireLocalField dualEntireQuotientMeasurable dualEntireTopology dualEntireUnipotentBorel dualEntireUnipotentMeasurable dualEntireValuation entireCoefficientGroupBorel entireCoefficientGroupMeasurable entireCoefficientLocalField entireCoefficientQuotientMeasurable entireCoefficientTopology entireCoefficientUnipotentBorel entireCoefficientUnipotentMeasurable entireCoefficientValuation secondBlock_whittakerFamily symmetricLPolynomial_determinantComplexPower
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding CorankOneEntireSliceStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockSecondWhittakerDeformationStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnramifiedTwistLFactorStatement WhittakerRowSliceCompactSupportStatement continuous_determinantOrder continuous_ord_units corankOneEntireSlice determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicPairLPolynomial_unramified_of_transport isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isPadicSymmetricLPolynomial_unramified_of_transport measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockSecondDeformedBlocks twoBlockSecondDeformedBlocks_zero twoBlockSecondDeformedInduced unramifiedTwistLFactor unramifiedTwistLFactor_of_transport whittakerRowSliceCompactSupport zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.ParameterSpecialization

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance dualEntireGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F) := borel _
local instance dualEntireGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F) := ⟨rfl⟩
local instance dualEntireUnipotentMeasurable (r : ℕ) :
    MeasurableSpace (upperUnipotent (r + 1) F) := borel _
local instance dualEntireUnipotentBorel (r : ℕ) :
    BorelSpace (upperUnipotent (r + 1) F) := ⟨rfl⟩
local instance dualEntireQuotientMeasurable (r : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient r F) := borel _

/-- A fixed right translation conjugates one common compact open level. -/
theorem HasCommonCompactOpenRightLevel.translate
    {r : ℕ} {ψ : UnitaryAdditiveCharacter F}
    {U : ℂ → WhittakerFunctions ψ r}
    (hU : HasCommonCompactOpenRightLevel F U)
    (a : Langlands.GeneralLinear (r + 1) F) :
    HasCommonCompactOpenRightLevel F (fun z => translateWhittaker ψ r (U z) a) := by
  obtain ⟨K, hKo, hKc, hK⟩ := hU
  let e : Langlands.GeneralLinear (r + 1) F ≃ₜ
      Langlands.GeneralLinear (r + 1) F :=
    (Homeomorph.mulLeft a⁻¹).trans (Homeomorph.mulRight a)
  let L := K.comap (MulAut.conj a⁻¹).toMonoidHom
  have hL : (L : Set (Langlands.GeneralLinear (r + 1) F)) = e ⁻¹' K := by
    ext k
    simp [L, e]
  refine ⟨L, ?_, ?_, ?_⟩
  · rw [hL]
    exact e.isOpen_preimage.mpr hKo
  · rw [hL]
    exact e.isCompact_preimage.mpr hKc
  · intro z g k
    have hk : a⁻¹ * k.val * a ∈ K := by
      have hk' := k.property
      change a⁻¹ * k.val * (a⁻¹)⁻¹ ∈ K at hk'
      simpa only [inv_inv] using hk'
    change (U z).val ((g * k.val) * a) = (U z).val (g * a)
    have heq : (g * k.val) * a = (g * a) * (a⁻¹ * k.val * a) := by
      simp only [mul_assoc, mul_inv_cancel_left]
    rw [heq]
    exact hK z (g * a) ⟨_, hk⟩

/-- Inverse transpose pulls one common compact open level back to a common
compact open level for the actual first dual functions. -/
theorem HasCommonCompactOpenRightLevel.firstDual
    {r : ℕ} {ψ : UnitaryAdditiveCharacter F}
    {U : ℂ → WhittakerFunctions ψ r}
    (hU : HasCommonCompactOpenRightLevel F U) :
    HasCommonCompactOpenRightLevel F (fun z => firstDualFunction ψ r (U z)) := by
  obtain ⟨K, hKo, hKc, hK⟩ := hU
  let e := inverseTransposeContinuous (r + 1) F
  let L := K.comap e.toMonoidHom
  refine ⟨L, e.toHomeomorph.isOpen_preimage.mpr hKo,
    e.toHomeomorph.isCompact_preimage.mpr hKc, ?_⟩
  intro z g k
  change (U z).val (weylLong (r + 1) F *
      inverseTranspose (r + 1) F (g * k.val)) =
    (U z).val (weylLong (r + 1) F *
      inverseTranspose (r + 1) F g)
  rw [map_mul, ← mul_assoc]
  exact hK z _ ⟨e k.val, k.property⟩

/-- The actual first dual transform, followed by the block Weyl translation
in the adjacent functional equation. -/
def adjacentRankDualWhittakerFamily
    (ψ : UnitaryAdditiveCharacter F) (r : ℕ)
    (U : ℂ → WhittakerFunctions ψ (r + 1)) :
    ℂ → WhittakerFunctions (ψ.scale (-1)) (r + 1) :=
  fun z => translateWhittaker (ψ.scale (-1)) (r + 1)
    (firstDualFunction ψ (r + 1) (U z))
    (blockWeylAt r (r + 1) (Nat.lt_succ_self r))

/-- The actual translated dual family retains a common compact open right
level and pointwise entire parameter dependence. -/
theorem adjacentRankDualWhittakerFamily_level_entire
    (ψ : UnitaryAdditiveCharacter F) (r : ℕ)
    (U : ℂ → WhittakerFunctions ψ (r + 1))
    (hK : HasCommonCompactOpenRightLevel F U)
    (hU : ∀ g z, AnalyticAt ℂ (fun u => (U u).val g) z) :
    HasCommonCompactOpenRightLevel F (adjacentRankDualWhittakerFamily F ψ r U) ∧
      ∀ g z, AnalyticAt ℂ
        (fun u => (adjacentRankDualWhittakerFamily F ψ r U u).val g) z := by
  refine ⟨(hK.firstDual F).translate F _, ?_⟩
  intro g z
  exact hU _ z

/-- The literal coefficients of the actual adjacent dual integral at spectral
parameter zero, for the same original test model vector. -/
def adjacentRankDualCoefficientFamily {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Measure (LeftUnipotentQuotient r F))
    (Wprime : InverseWhittakerFunctions ψ r)
    (U : ℂ → WhittakerFunctions ψ (r + 1)) : ℂ → BilateralLaurentSeries :=
  corankCoefficientFamily F (ψ.scale (-1)) ν
    (secondDualFunction ψ r Wprime) (adjacentRankDualWhittakerFamily F ψ r U)

/-- The published corank slice theorem applies to the actual dual test model
and actual translated dual family, giving both integrability and entire
dependence of every literal dual determinant-slice coefficient. -/
theorem adjacentRankDualCoefficientFamily_integrable_entire
    (ψ : UnitaryAdditiveCharacter F) (r : ℕ)
    [Measure.IsMulRightInvariant (unipotentHaar F r)]
    (ν : Measure (LeftUnipotentQuotient r F))
    (hν : IsCompatible (upperUnipotent (r + 1) F)
      (generalLinearHaar F r) (unipotentHaar F r) ν)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (hτ : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ)
    (ℓ : glInverseFunctionals ψ r τ)
    (Wprime : (coefficientModel τ ℓ).toSubmodule)
    (U : ℂ → WhittakerFunctions ψ (r + 1))
    (hK : HasCommonCompactOpenRightLevel F U)
    (hU : ∀ g z, AnalyticAt ℂ (fun u => (U u).val g) z) :
    (∀ z, SliceIntegrable (⟨⟩ : LocalFieldData F) ν
      (corankOneIntegrand (ψ.scale (-1))
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        (adjacentRankDualWhittakerFamily F ψ r U z)
        (secondDualFunction ψ r Wprime.val) 0)) ∧
      EntireCoefficientFamily (adjacentRankDualCoefficientFamily F ψ ν Wprime.val U) := by
  have hτd : IsOfWhittakerType r
      (inverseStandardCharacter (ψ.scale (-1)) r) (inverseTransposePullback τ) := by
    simpa only [inverseStandardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback_inverse ψ τ hτ
  obtain ⟨hKd, hUd⟩ := adjacentRankDualWhittakerFamily_level_entire F ψ r U hK hU
  exact corankCoefficientFamily_integrable_entire F (ψ.scale (-1)) r ν hν
    (inverseTransposePullback τ) hτd (secondDualFunctional ψ τ ℓ)
    (secondDualModelMap ψ τ ℓ Wprime) (adjacentRankDualWhittakerFamily F ψ r U)
    hKd hUd

end Langlands.AllField.RankinSelberg.Padic
