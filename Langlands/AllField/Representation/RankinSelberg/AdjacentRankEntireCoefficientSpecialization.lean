import Langlands.Representation.RankinSelberg.AdjacentRankEntireCoefficientSpecialization
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankClearingKernel
import Langlands.AllField.Representation.RankinSelberg.CorankOneEntireSliceProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockSecondWhittakerDeformationStatement
/-! Actual corank coefficient families and specialization of their Laurent clearing. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding HasCommonCompactOpenRightLevel clearingKernelTopology corankCoefficientFamily corankCoefficientFamily_integrable_entire entireCoefficientGroupBorel entireCoefficientGroupMeasurable entireCoefficientLocalField entireCoefficientQuotientMeasurable entireCoefficientTopology entireCoefficientUnipotentBorel entireCoefficientUnipotentMeasurable entireCoefficientValuation secondBlock_whittakerFamily symmetricLPolynomial_determinantComplexPower
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

local instance entireCoefficientGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F) := borel _
local instance entireCoefficientGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F) := ⟨rfl⟩
local instance entireCoefficientUnipotentMeasurable (r : ℕ) :
    MeasurableSpace (upperUnipotent (r + 1) F) := borel _
local instance entireCoefficientUnipotentBorel (r : ℕ) :
    BorelSpace (upperUnipotent (r + 1) F) := ⟨rfl⟩
local instance entireCoefficientQuotientMeasurable (r : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient r F) := borel _

local notation "T" => (⟨⟩ : LocalFieldData F)
local notation "abv" => normalizedAbsoluteValue T

/-- One compact open right level for the whole actual Whittaker family. -/
def HasCommonCompactOpenRightLevel {r : ℕ}
    {ψ : UnitaryAdditiveCharacter F} (U : ℂ → WhittakerFunctions ψ r) : Prop :=
  ∃ K : Subgroup (Langlands.GeneralLinear (r + 1) F),
    IsOpen (K : Set (Langlands.GeneralLinear (r + 1) F)) ∧
    IsCompact (K : Set (Langlands.GeneralLinear (r + 1) F)) ∧
    ∀ (u : ℂ) (g : Langlands.GeneralLinear (r + 1) F) (k : K),
      (U u).val (g * k) = (U u).val g

/-- The literal determinant-slice coefficients at spectral parameter zero. -/
def corankCoefficientFamily {r : ℕ} (ψ : UnitaryAdditiveCharacter F)
    (ν : Measure (LeftUnipotentQuotient r F))
    (Wprime : InverseWhittakerFunctions ψ r)
    (U : ℂ → WhittakerFunctions ψ (r + 1)) : ℂ → BilateralLaurentSeries :=
  fun u m => sliceCoefficient T ν (corankOneIntegrand ψ abv (U u) Wprime 0) m

/-- The published corank slice theorem supplies integrability and entire
dependence for the actual coefficient family, with its original measure. -/
theorem corankCoefficientFamily_integrable_entire
    (ψ : UnitaryAdditiveCharacter F) (r : ℕ)
    [Measure.IsMulRightInvariant (unipotentHaar F r)]
    (ν : Measure (LeftUnipotentQuotient r F))
    (hν : IsCompatible (upperUnipotent (r + 1) F)
      (generalLinearHaar F r) (unipotentHaar F r) ν)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (hτ : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ)
    (ℓ : glInverseFunctionals ψ r τ) (Wprime : (coefficientModel τ ℓ).toSubmodule)
    (U : ℂ → WhittakerFunctions ψ (r + 1))
    (hK : HasCommonCompactOpenRightLevel F U)
    (hU : ∀ g u, AnalyticAt ℂ (fun z => (U z).val g) u) :
    (∀ u, SliceIntegrable T ν (corankOneIntegrand ψ abv (U u) Wprime.val 0)) ∧
      EntireCoefficientFamily (corankCoefficientFamily F ψ ν Wprime.val U) := by
  have hs := corankOneEntireSlice F ψ r ν hν V τ hτ ℓ Wprime U hK hU
  exact ⟨fun u m => (hs m).1 u, fun m u => (hs m).2 u⟩

/-- The second-block deformation proposition extends every actual coefficient
image vector to Whittaker functions, retaining all coefficient realizations. -/
theorem secondBlock_whittakerFamily
    (hdeform : TwoBlockSecondWhittakerDeformationStatement.{uF,uW})
    (ψ : UnitaryAdditiveCharacter F) (t : ℕ)
    (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i))
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (ℓ₀ : glFunctionals ψ t (twoBlockSecondDeformedInduced F m h σ 0))
    (hℓ₀ : ℓ₀.val ≠ 0)
    (W₀ : (coefficientModel (twoBlockSecondDeformedInduced F m h σ 0) ℓ₀).toSubmodule) :
    ∃ U : ℂ → WhittakerFunctions ψ t,
      U 0 = W₀.val ∧
      (∀ u : ℂ, ∃ ℓ : glFunctionals ψ t (twoBlockSecondDeformedInduced F m h σ u),
        ℓ.val ≠ 0 ∧ ∃ v, coefficientMap (twoBlockSecondDeformedInduced F m h σ u) ℓ v =
          U u) ∧
      HasCommonCompactOpenRightLevel F U ∧
      ∀ g u, AnalyticAt ℂ (fun z => (U z).val g) u := by
  obtain ⟨v₀, hv₀⟩ :=
    modelMap_surjective (twoBlockSecondDeformedInduced F m h σ 0) ℓ₀ W₀
  obtain ⟨Wu, hzero, hcoeff, hlevel, hanalytic⟩ :=
    hdeform F ψ t m h σ hσ ℓ₀ hℓ₀ v₀
  let U : ℂ → WhittakerFunctions ψ t := fun u =>
    ⟨Wu u, by
      obtain ⟨ℓ, -, v, hv⟩ := hcoeff u
      intro n g
      change Wu u ((n : Langlands.GeneralLinear (t + 1) F) * g) =
        (standardCharacter ψ t n : ℂ) * Wu u g
      rw [hv, hv, map_mul, Module.End.mul_apply]
      exact ℓ.property n _⟩
  refine ⟨U, ?_, ?_, hlevel, hanalytic⟩
  · apply Subtype.ext
    funext g
    have hvalue := congrArg (fun w => w.val.val g) hv₀
    exact (hzero g).trans hvalue
  · intro u
    obtain ⟨ℓ, hℓ, v, hv⟩ := hcoeff u
    refine ⟨ℓ, hℓ, v, ?_⟩
    apply Subtype.ext
    funext g
    exact (hv g).symm

end Langlands.AllField.RankinSelberg.Padic
