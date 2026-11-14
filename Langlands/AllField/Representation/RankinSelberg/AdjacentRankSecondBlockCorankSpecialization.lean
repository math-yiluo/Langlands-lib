import Langlands.Representation.RankinSelberg.AdjacentRankSecondBlockCorankSpecialization
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankEntireCoefficientSpecialization
/-! Entire corank coefficients of the actual second-block family and their initial clearing. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding HasCommonCompactOpenRightLevel SecondBlockCorankRealRayClearing clearingKernelTopology corankCoefficientFamily corankCoefficientFamily_integrable_entire corankCoefficientSeries entireCoefficientGroupBorel entireCoefficientGroupMeasurable entireCoefficientLocalField entireCoefficientQuotientMeasurable entireCoefficientTopology entireCoefficientUnipotentBorel entireCoefficientUnipotentMeasurable entireCoefficientValuation secondBlock_corankClearing_at_zero secondBlock_entireCorankFamily secondBlock_whittakerFamily secondCorankGroupBorel secondCorankGroupMeasurable secondCorankLocalField secondCorankQuotientMeasurable secondCorankTopology secondCorankUnipotentBorel secondCorankUnipotentMeasurable secondCorankValuation symmetricLPolynomial_determinantComplexPower
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
open scoped BigOperators

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance secondCorankGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F) := borel _
local instance secondCorankGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F) := ⟨rfl⟩
local instance secondCorankUnipotentMeasurable (r : ℕ) :
    MeasurableSpace (upperUnipotent (r + 1) F) := borel _
local instance secondCorankUnipotentBorel (r : ℕ) :
    BorelSpace (upperUnipotent (r + 1) F) := ⟨rfl⟩
local instance secondCorankQuotientMeasurable (r : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient r F) := borel _

local notation "T" => (⟨⟩ : LocalFieldData F)
local notation "abv" => normalizedAbsoluteValue T

/-- The actual bilateral coefficient series of one corank integral. -/
def corankCoefficientSeries {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Measure (LeftUnipotentQuotient r F))
    (U : WhittakerFunctions ψ (r + 1)) (Wprime : InverseWhittakerFunctions ψ r) :
    BilateralLaurentSeries :=
  fun m => sliceCoefficient T ν (corankOneIntegrand ψ abv U Wprime 0) m

/-- Formal clearing on a real ray for every actual coefficient of the second
deformed lower induction. This is an input, separate from integral analyticity. -/
def SecondBlockCorankRealRayClearing
    {r : ℕ} (ψ : UnitaryAdditiveCharacter F)
    (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = (r + 1) + 1)
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i))
    (ν : Measure (LeftUnipotentQuotient r F))
    (Wprime : InverseWhittakerFunctions ψ r)
    (P₀ P₁ : Polynomial ℂ) (C : ℝ) : Prop :=
  ∀ u : ℝ, C < u →
    ∀ ℓ : glFunctionals ψ (r + 1)
      (twoBlockSecondDeformedInduced F m h σ (u : ℂ)), ℓ.val ≠ 0 →
    ∀ v, ∃ R : LaurentPolynomial ℂ,
      BilateralLaurentSeries.ofLaurentPolynomial R =
        spectralClearingKernel (⟨⟩ : LocalFieldData F).residueCardinality
          P₀ P₁ (u : ℂ) •
        corankCoefficientSeries F ψ ν
          (coefficientMap (twoBlockSecondDeformedInduced F m h σ (u : ℂ)) ℓ v) Wprime

/-- Every original coefficient extends to an actual second-block Whittaker
family whose corank slices are integrable and entire for the supplied measure. -/
theorem secondBlock_entireCorankFamily
    (hdeform : TwoBlockSecondWhittakerDeformationStatement.{uF,uW})
    (ψ : UnitaryAdditiveCharacter F) (r : ℕ)
    [Measure.IsMulRightInvariant (unipotentHaar F r)]
    (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = (r + 1) + 1)
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i))
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (ℓ₀ : glFunctionals ψ (r + 1) (twoBlockSecondDeformedInduced F m h σ 0))
    (hℓ₀ : ℓ₀.val ≠ 0)
    (W₀ : (coefficientModel (twoBlockSecondDeformedInduced F m h σ 0) ℓ₀).toSubmodule)
    (ν : Measure (LeftUnipotentQuotient r F))
    (hν : IsCompatible (upperUnipotent (r + 1) F)
      (generalLinearHaar F r) (unipotentHaar F r) ν)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (hτ : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ)
    (ℓ : glInverseFunctionals ψ r τ) (Wprime : (coefficientModel τ ℓ).toSubmodule) :
    ∃ U : ℂ → WhittakerFunctions ψ (r + 1),
      U 0 = W₀.val ∧
      (∀ u : ℂ, ∃ ℓu : glFunctionals ψ (r + 1)
          (twoBlockSecondDeformedInduced F m h σ u),
        ℓu.val ≠ 0 ∧ ∃ v,
          coefficientMap (twoBlockSecondDeformedInduced F m h σ u) ℓu v = U u) ∧
      HasCommonCompactOpenRightLevel F U ∧
      (∀ g u, AnalyticAt ℂ (fun z => (U z).val g) u) ∧
      (∀ u, SliceIntegrable T ν (corankOneIntegrand ψ abv (U u) Wprime.val 0)) ∧
      EntireCoefficientFamily (corankCoefficientFamily F ψ ν Wprime.val U) := by
  obtain ⟨U, hzero, hcoeff, hK, hU⟩ :=
    secondBlock_whittakerFamily F hdeform ψ (r + 1) m h σ hσ ℓ₀ hℓ₀ W₀
  obtain ⟨hint, hent⟩ :=
    corankCoefficientFamily_integrable_entire F ψ r ν hν τ hτ ℓ Wprime U hK hU
  exact ⟨U, hzero, hcoeff, hK, hU, hint, hent⟩

/-- Clearing every actual deformed coefficient above a real bound clears the
specified original coefficient by the original product polynomial. -/
theorem secondBlock_corankClearing_at_zero
    (hdeform : TwoBlockSecondWhittakerDeformationStatement.{uF,uW})
    (ψ : UnitaryAdditiveCharacter F) (r : ℕ)
    [Measure.IsMulRightInvariant (unipotentHaar F r)]
    (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = (r + 1) + 1)
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i))
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (ℓ₀ : glFunctionals ψ (r + 1) (twoBlockSecondDeformedInduced F m h σ 0))
    (hℓ₀ : ℓ₀.val ≠ 0)
    (W₀ : (coefficientModel (twoBlockSecondDeformedInduced F m h σ 0) ℓ₀).toSubmodule)
    (ν : Measure (LeftUnipotentQuotient r F))
    (hν : IsCompatible (upperUnipotent (r + 1) F)
      (generalLinearHaar F r) (unipotentHaar F r) ν)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (hτ : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ)
    (ℓ : glInverseFunctionals ψ r τ) (Wprime : (coefficientModel τ ℓ).toSubmodule)
    (P₀ P₁ : Polynomial ℂ) (C : ℝ)
    (hreal : SecondBlockCorankRealRayClearing F ψ m h σ ν Wprime.val P₀ P₁ C) :
    ∃ R : LaurentPolynomial ℂ,
      BilateralLaurentSeries.ofLaurentPolynomial R = (P₀ * P₁).toLaurent •
        corankCoefficientSeries F ψ ν W₀.val Wprime.val := by
  obtain ⟨U, hzero, hcoeff, -, -, -, hent⟩ :=
    secondBlock_entireCorankFamily F hdeform ψ r m h σ hσ ℓ₀ hℓ₀ W₀
      ν hν τ hτ ℓ Wprime
  have hclears : ∀ u : ℝ, C < u → ∃ R : LaurentPolynomial ℂ,
      BilateralLaurentSeries.ofLaurentPolynomial R =
        spectralClearingKernel (⟨⟩ : LocalFieldData F).residueCardinality
          P₀ P₁ (u : ℂ) • corankCoefficientFamily F ψ ν Wprime.val U (u : ℂ) := by
    intro u hu
    obtain ⟨ℓu, hℓu, v, hv⟩ := hcoeff (u : ℂ)
    obtain ⟨R, hR⟩ := hreal u hu ℓu hℓu v
    refine ⟨R, ?_⟩
    rw [hv] at hR
    exact hR
  obtain ⟨R, hR⟩ := spectralKernel_laurent_clearing_at_zero
    (⟨⟩ : LocalFieldData F).residueCardinality_gt_one P₀ P₁
      (corankCoefficientFamily F ψ ν Wprime.val U) hent C hclears
  refine ⟨R, ?_⟩
  change BilateralLaurentSeries.ofLaurentPolynomial R = (P₀ * P₁).toLaurent •
    corankCoefficientSeries F ψ ν (U 0) Wprime.val at hR
  rw [hzero] at hR
  exact hR

end Langlands.AllField.RankinSelberg.Padic
