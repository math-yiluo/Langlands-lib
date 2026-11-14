import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentConvergence
import Langlands.AllField.LocalField.SmoothCharacterNormProofSupplement
import Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.AllField.Representation.Geometric.GeometricLemmaStatement
import Langlands.AllField.Representation.Parabolic.NormalizedJacquetStatementSupplement
import Langlands.AllField.Representation.RankinSelberg.NormalizedCompactIntegrationProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentSlices
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData
import Langlands.AllField.Representation.RankinSelberg.UnequalRankAnalyticProof
import Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement
import Langlands.AllField.Representation.Unramified.SphericalConstituentExistenceProof
import Langlands.AllField.Representation.Whittaker.MirabolicUnitTestProof
/-!
# Spectral series of the original and transformed small integrals

For representations of full Whittaker type and nonzero functionals, the actual
unequal-rank integral of every pair of coefficient-image vectors converges absolutely on
a right half-plane, by the published unequal-rank analytic theorem; there it is the
absolutely summable series of its determinant-slice coefficients. The transformed
integral is the same object for the inverse-transpose pair, the inverse additive
character and the exchanged blocks.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
open Langlands.RankinSelberg.TwoBlockFirstBlockLaurent hiding dualIntegrand_integrableOn_slice dualSmallIntegral_series smallIntegral_series smallIntegrand_integrableOn_slice unequalRankIntegrandAt unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankSliceCoefficient unequalRankSliceCoefficientAt unequalRank_sliceExpansion
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankSliceExpansionStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion finiteFunctionMellin finiteFunctionShellSeries hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice unequalRankAnalytic unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

variable (F : Type uF) [Field F]

/-- The slice coefficient at a fixed large rank, with the rank equality transporting
only types. -/
def unequalRankSliceCoefficientAt [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {n r : ℕ} (j k : ℕ) (hr : r = n + (j + k + 1))
    (ψ : UnitaryAdditiveCharacter F)
    (μ : letI := borel (LeftUnipotentQuotient n F)
      Measure (LeftUnipotentQuotient n F))
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (W : WhittakerFunctions ψ r)
    (W' : InverseWhittakerFunctions ψ n)
    (m : ℤ) : ℂ := by
  subst hr
  exact unequalRankSliceCoefficient (⟨⟩ : LocalFieldData F) j k ψ μ ν W W' m

/-- The actual small integral of coefficient-image vectors is, on a right half-plane, the
absolutely summable series of its slice coefficients. -/
theorem smallIntegral_series [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {n r : ℕ} (j k : ℕ) (hr : r = n + (j + k + 1)) :
    let T := (⟨⟩ : LocalFieldData F)
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI : MeasurableSpace (GeneralLinear (n + 1) F) := borel _
    letI : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
    letI : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    letI : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
    letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F) (μ : Measure (LeftUnipotentQuotient n F)),
      IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
        (unipotentHaar F n) μ → SigmaFinite μ →
      ∀ (ν : AdditiveHaarMeasure F)
        {V : Type uV} [AddCommGroup V] [Module ℂ V]
        {W : Type uW} [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (GeneralLinear (r + 1) F) V)
        (σ : Representation ℂ (GeneralLinear (n + 1) F) W),
        IsOfWhittakerType r (standardCharacter ψ r) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          ∀ (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule),
            ∃ C : ℝ, ∀ s : ℂ, C < s.re →
              Summable (fun m : ℤ =>
                ‖unequalRankSliceCoefficientAt F j k hr ψ μ (rectangularMeasure ν j (n + 1))
                    f.val f'.val m * spectralPoint T.residueCardinality s ^ m‖) ∧
              HasSum (fun m : ℤ =>
                unequalRankSliceCoefficientAt F j k hr ψ μ (rectangularMeasure ν j (n + 1))
                    f.val f'.val m * spectralPoint T.residueCardinality s ^ m)
                (unequalRankIntegralAt j k hr ψ (normalizedAbsoluteValue T) μ
                  (rectangularMeasure ν j (n + 1)) f.val f'.val s) := by
  subst hr
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear (n + 1) F) := borel _
  let : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro ψ μ hμ hμσ ν V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ' f f'
  have := Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  obtain ⟨hconv, -, -, -⟩ :=
    unequalRankAnalytic.{uF, uV, uW} F T n j k ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
  obtain ⟨a, ha⟩ := hconv f f'
  exact ⟨a, fun s hs => unequalRank_sliceExpansion T j k ψ μ (rectangularMeasure ν j (n + 1))
    f.val f'.val s (ha s hs)⟩

/-- The actual transformed small integral is, on a right half-plane, the absolutely
summable series of the slice coefficients of the inverse-transpose pair. -/
theorem dualSmallIntegral_series [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {n r : ℕ} (hnr : n < r) (j k : ℕ)
    (hr : r = n + (j + k + 1)) :
    let T := (⟨⟩ : LocalFieldData F)
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI : MeasurableSpace (GeneralLinear (n + 1) F) := borel _
    letI : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
    letI : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    letI : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
    letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F) (μ : Measure (LeftUnipotentQuotient n F)),
      IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
        (unipotentHaar F n) μ → SigmaFinite μ →
      ∀ (ν : AdditiveHaarMeasure F)
        {V : Type uV} [AddCommGroup V] [Module ℂ V]
        {W : Type uW} [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (GeneralLinear (r + 1) F) V)
        (σ : Representation ℂ (GeneralLinear (n + 1) F) W),
        IsOfWhittakerType r (standardCharacter ψ r) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          ∀ (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule),
            ∃ C : ℝ, ∀ s : ℂ, C < s.re →
              Summable (fun m : ℤ =>
                ‖unequalRankSliceCoefficientAt F k j (by omega) (ψ.scale (-1)) μ
                    (rectangularMeasure ν k (n + 1))
                    (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r f.val)
                      (blockWeylAt n r hnr))
                    (secondDualFunction ψ n f'.val) m *
                  spectralPoint T.residueCardinality s ^ m‖) ∧
              HasSum (fun m : ℤ =>
                unequalRankSliceCoefficientAt F k j (by omega) (ψ.scale (-1)) μ
                    (rectangularMeasure ν k (n + 1))
                    (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r f.val)
                      (blockWeylAt n r hnr))
                    (secondDualFunction ψ n f'.val) m *
                  spectralPoint T.residueCardinality s ^ m)
                (dualUnequalRankModelIntegralAt hnr j k hr ψ (normalizedAbsoluteValue T) μ ν
                  π σ ℓ ℓ' f f' s) := by
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear (n + 1) F) := borel _
  let : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro ψ μ hμ hμσ ν V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ' f f'
  have hπdual : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r)
      (inverseTransposePullback π) := by
    simpa only [standardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback ψ π hπ
  have hσdual : IsOfWhittakerType n (inverseStandardCharacter (ψ.scale (-1)) n)
      (inverseTransposePullback σ) := by
    simpa only [inverseStandardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback_inverse ψ σ hσ
  exact smallIntegral_series F k j (by omega) (ψ.scale (-1)) μ hμ hμσ ν
    (inverseTransposePullback π) (inverseTransposePullback σ) hπdual hσdual
    (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ')
    (firstDualFunctional_ne_zero ψ π hℓ) (secondDualFunctional_ne_zero ψ σ hℓ')
    (translatedFirstDualModelEquiv ψ π ℓ (blockWeylAt n r hnr) f)
    (secondDualModelMap ψ σ ℓ' f')

/-- The unequal-rank integrand at a fixed large rank, with the rank equality transporting
only types. -/
def unequalRankIntegrandAt [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {n r : ℕ} (j k : ℕ) (hr : r = n + (j + k + 1))
    (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ)
    (W : WhittakerFunctions ψ r)
    (W' : InverseWhittakerFunctions ψ n)
    (s : ℂ) (x : Matrix (Fin j) (Fin (n + 1)) F) :
    LeftUnipotentQuotient n F → ℂ := by
  subst hr
  exact unequalRankIntegrand ψ abv j k W W' s x

/-- On every determinant slice, the inner rectangular integral at `s = 0` of the actual
small integrand of coefficient-image vectors is integrable. -/
theorem smallIntegrand_integrableOn_slice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {n r : ℕ} (j k : ℕ) (hr : r = n + (j + k + 1)) :
    let T := (⟨⟩ : LocalFieldData F)
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI : MeasurableSpace (GeneralLinear (n + 1) F) := borel _
    letI : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
    letI : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    letI : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
    letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F) (μ : Measure (LeftUnipotentQuotient n F)),
      IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
        (unipotentHaar F n) μ → SigmaFinite μ →
      ∀ (ν : AdditiveHaarMeasure F)
        {V : Type uV} [AddCommGroup V] [Module ℂ V]
        {W : Type uW} [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (GeneralLinear (r + 1) F) V)
        (σ : Representation ℂ (GeneralLinear (n + 1) F) W),
        IsOfWhittakerType r (standardCharacter ψ r) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          ∀ (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule)
            (m : ℤ),
            Integrable (fun q => ∫ x, unequalRankIntegrandAt F j k hr ψ
                (normalizedAbsoluteValue T) f.val f'.val 0 x q ∂rectangularMeasure ν j (n + 1))
              (μ.restrict (determinantSlice T n m)) := by
  subst hr
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear (n + 1) F) := borel _
  let : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro ψ μ hμ hμσ ν V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ' f f' m
  have := Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  obtain ⟨hconv, -, -, -⟩ :=
    unequalRankAnalytic.{uF, uV, uW} F T n j k ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ'
  obtain ⟨a, ha⟩ := hconv f f'
  let s : ℂ := ((a + 1 : ℝ) : ℂ)
  have hs : a < s.re := by simp [s]
  have hG : Integrable (fun q => ∫ x, unequalRankIntegrand ψ (normalizedAbsoluteValue T) j k
      f.val f'.val s x q ∂rectangularMeasure ν j (n + 1)) μ :=
    (ha s hs).integral_prod_left
  have hX : spectralPoint T.residueCardinality s ^ m ≠ 0 :=
    zpow_ne_zero _ (spectralPoint_ne_zero_of_pos
      (Nat.zero_lt_one.trans T.residueCardinality_gt_one) s)
  refine ((hG.restrict).mul_const ((spectralPoint T.residueCardinality s ^ m)⁻¹)).congr ?_
  refine (ae_restrict_iff' (measurableSet_determinantSlice T n m)).mpr
    (Filter.Eventually.of_forall fun q hq => ?_)
  change (∫ x, unequalRankIntegrand ψ (normalizedAbsoluteValue T) j k f.val f'.val s x q
      ∂rectangularMeasure ν j (n + 1)) * (spectralPoint T.residueCardinality s ^ m)⁻¹ =
    ∫ x, unequalRankIntegrand ψ (normalizedAbsoluteValue T) j k f.val f'.val 0 x q
      ∂rectangularMeasure ν j (n + 1)
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [unequalRankIntegrand_eq_mul_spectralPoint_zpow T j k ψ f.val f'.val s x m q hq,
    mul_assoc, mul_inv_cancel₀ hX, mul_one]

/-- On every determinant slice, the inner integral at `s = 0` of the actual transformed
small integrand is integrable. -/
theorem dualIntegrand_integrableOn_slice [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {n r : ℕ} (hnr : n < r) (j k : ℕ)
    (hr : r = n + (j + k + 1)) :
    let T := (⟨⟩ : LocalFieldData F)
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI : MeasurableSpace (GeneralLinear (n + 1) F) := borel _
    letI : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
    letI : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    letI : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
    letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F) (μ : Measure (LeftUnipotentQuotient n F)),
      IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
        (unipotentHaar F n) μ → SigmaFinite μ →
      ∀ (ν : AdditiveHaarMeasure F)
        {V : Type uV} [AddCommGroup V] [Module ℂ V]
        {W : Type uW} [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (GeneralLinear (r + 1) F) V)
        (σ : Representation ℂ (GeneralLinear (n + 1) F) W),
        IsOfWhittakerType r (standardCharacter ψ r) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          ∀ (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule)
            (m : ℤ),
            Integrable (fun q => ∫ z, unequalRankIntegrandAt F k j (by omega) (ψ.scale (-1))
                (normalizedAbsoluteValue T)
                (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r f.val)
                  (blockWeylAt n r hnr))
                (secondDualFunction ψ n f'.val) 0 z q ∂rectangularMeasure ν k (n + 1))
              (μ.restrict (determinantSlice T n m)) := by
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear (n + 1) F) := borel _
  let : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro ψ μ hμ hμσ ν V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ' f f' m
  have hπdual : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r)
      (inverseTransposePullback π) := by
    simpa only [standardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback ψ π hπ
  have hσdual : IsOfWhittakerType n (inverseStandardCharacter (ψ.scale (-1)) n)
      (inverseTransposePullback σ) := by
    simpa only [inverseStandardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback_inverse ψ σ hσ
  exact smallIntegrand_integrableOn_slice F k j (by omega) (ψ.scale (-1)) μ hμ hμσ ν
    (inverseTransposePullback π) (inverseTransposePullback σ) hπdual hσdual
    (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ')
    (firstDualFunctional_ne_zero ψ π hℓ) (secondDualFunctional_ne_zero ψ σ hℓ')
    (translatedFirstDualModelEquiv ψ π ℓ (blockWeylAt n r hnr) f)
    (secondDualModelMap ψ σ ℓ' f') m

end Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
