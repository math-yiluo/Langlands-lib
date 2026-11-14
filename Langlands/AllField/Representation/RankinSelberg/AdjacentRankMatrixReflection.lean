import Langlands.Representation.RankinSelberg.AdjacentRankMatrixReflection
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankDualModelZetaCoefficient
/-! The actual reflected square-test scalar in the dual adjacent-rank formula. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankModelConverges AdjacentRankShellConvolutionAt AdjacentRankShellLowerBounds adjacentRankBeforeShearKernel adjacentRankBeforeShearKernel_mk adjacentRankCompact_middleAverage adjacentRankCompact_middleAverage_and_dual adjacentRankDualInnerSliceIntegral adjacentRankDualMatrixCoefficient_minusOne adjacentRankDualMatrixReflectionScalar adjacentRankDualMiddleAverage adjacentRankDualMiddleAverage_eq adjacentRankInnerMultiplier adjacentRankInnerMultiplier_mul adjacentRankInnerSliceWeight adjacentRankInnerSliceWeight_mul adjacentRankInnerSlice_matchedFiniteSeparation adjacentRankJointShell adjacentRankJointShellKernel adjacentRankJointShellKernel_mk adjacentRankJointShellKernel_mk_eq_innerSlice adjacentRankMatrix_reflectedRationalValue adjacentRankMatrix_reflection adjacentRankModelConverges_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegral_mul adjacentRankModelIntegral_separated_rankInclusion_raw adjacentRankModelIntegral_separated_rankInclusion_weighted adjacentRankModelMap adjacentRankModelMapBorel adjacentRankModelMapDisconnected adjacentRankModelMapGLMeasurable adjacentRankModelMapLocalField adjacentRankModelMapMeasurable adjacentRankModelMapT2 adjacentRankModelMapTopology adjacentRankModelMapValuative adjacentRankModelMap_apply adjacentRankModelStarScalar adjacentRankModelStar_corankOneSlice_eq_before adjacentRankModelStar_reflectedProduct_cancel adjacentRankModelStar_reflectionScalar_cancel adjacentRankModelStar_separated_rankInclusion adjacentRankModelStar_separated_rankInclusion_weighted adjacentRankModel_corankOneSlice_eq_before adjacentRankSeparatedTest_rho0_rankInclusion adjacentRankShell_finiteConvolution_of_innerSeparation adjacentRankShell_matchedFiniteConvolution adjacentRankShell_shear_fubini biSmoothModelCoefficient_minusOne compactCoefficientsBorel compactCoefficientsLocalField compactCoefficientsMeasurable compactCoefficientsTopology compactCoefficientsValuativeRel continuous_adjacentRankInnerMultiplier continuous_adjacentRankInnerSliceWeight continuous_adjacentRankJointShellKernel dualCompactFieldTopology dualCompactGroupBorel dualCompactGroupMeasurable dualCompactLocalField dualCompactValuativeRel dualModelFieldBorel dualModelFieldMeasurable dualModelFieldT2 dualModelFieldTopology dualModelFieldTotallyDisconnected dualModelGroupBorel dualModelGroupMeasurable dualModelLocalField dualModelValuativeRel dualRestrictionFieldBorel dualRestrictionFieldMeasurable dualRestrictionFieldT2 dualRestrictionFieldTopology dualRestrictionFieldTotallyDisconnected dualRestrictionGroupBorel dualRestrictionGroupMeasurable dualRestrictionLocalField dualRestrictionValuativeRel exists_adjacentRankInner_subgroup exists_matrixTest_determinantOrder_lowerBound exists_whittakerRow_determinantOrder_lowerBound hasCompactSupport_adjacentRankInnerSliceWeight hasCompactSupport_adjacentRankJointShellKernel hasCompactSupport_equalRankSlice innerSliceFieldTopology innerSliceGroupBorel innerSliceGroupMeasurable innerSliceLocalField innerSliceValuativeRel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_adjacentRankInnerSliceWeight_mul integrable_adjacentRankJointShellKernel integrable_equalRankSlice integral_eq_sum_determinantSlices inverseCoefficientAsScaledStandard isClopen_adjacentRankJointShell jointShellFieldT2 jointShellFieldTopology jointShellGroupBorelSpace jointShellGroupMeasurableSpace jointShellGroupSecondCountable jointShellGroupSigmaCompact jointShellLocalField jointShellQuotientBorelSpace jointShellQuotientMeasurableSpace jointShellQuotientT2 jointShellValuativeRel matchedInnerFieldTopology matchedInnerGroupBorel matchedInnerGroupMeasurable matchedInnerGroupSecondCountable matchedInnerGroupSigmaCompact matchedInnerLocalField matchedInnerValuativeRel matchedShellFieldT2 matchedShellFieldTopology matchedShellGroupBorel matchedShellGroupMeasurable matchedShellGroupSecondCountable matchedShellGroupSigmaCompact matchedShellLocalField matchedShellQuotientLocallyCompact matchedShellQuotientMeasurable matchedShellQuotientSecondCountable matchedShellUnipotentBorel matchedShellUnipotentMeasurable matchedShellValuativeRel modelZetaFieldBorel modelZetaFieldMeasurable modelZetaFieldT2 modelZetaFieldTopology modelZetaFieldTotallyDisconnected modelZetaGroupBorel modelZetaGroupMeasurable modelZetaLocalField modelZetaValuativeRel quotientShearFieldT2 quotientShearFieldTopology quotientShearGroupBorel quotientShearGroupMeasurable quotientShearGroupSecondCountable quotientShearGroupSigmaCompact quotientShearLocalField quotientShearQuotientBorel quotientShearQuotientLocallyCompact quotientShearQuotientMeasurable quotientShearQuotientSecondCountable quotientShearUnipotentBorel quotientShearUnipotentMeasurable quotientShearValuativeRel reflectionFieldTopology reflectionGroupBorel reflectionGroupMeasurable reflectionLocalField reflectionValuativeRel shellConvolutionFieldTopology shellConvolutionLocalField shellConvolutionQuotientBorel shellConvolutionQuotientMeasurable shellConvolutionValuativeRel
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding AdjacentRankBaseModelStarIdentity AdjacentRankModelConvergenceStatement AdjacentRankModelConverges AdjacentRankModelStarStatement EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneGammaTwistStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankFullFourier adjacentRankFullFourier_inverseTranspose adjacentRankFullFourier_tmul adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegrand adjacentRankModelStar adjacentRankModelStarBase_of_pure_integrals adjacentRankModelStarIntegrabilityLocalInstance1 adjacentRankModelStarIntegrabilityLocalInstance2 adjacentRankModelStarIntegrabilityLocalInstance3 adjacentRankModelStarIntegrabilityLocalInstance4 adjacentRankModelStarIntegrabilityLocalInstance5 adjacentRankModelStarIntegrabilityLocalInstance6 adjacentRankModelStarIntegrabilityLocalInstance7 adjacentRankModelStarIntegrabilityLocalInstance8 adjacentRankModelStarIntegrabilityLocalInstance9 adjacentRankModelStarSourceFunction_regularity adjacentRankModelStarTargetFunction_regularity adjacentRankModelStar_base adjacentRankModelStar_equality_of_base adjacentRankModelStar_pure_right_averages adjacentRankPure_hasCompactSupport adjacentRankStarEquiv adjacentRankStarEquiv_tmul_evaluation adjacentRankTransformedIntegrand adjacentRankTransformedPure_hasCompactSupport adjacentRankTransformed_integrable_of_isSmooth adjacentRank_distribHaarChar adjacentRank_fullFourier_kernel_reflected_orbit adjacentRank_fullFourier_rowTranslate adjacentRank_inverseTranspose_unipotent_epsilon adjacentRank_kernel_reflected_right_orbit adjacentRank_kernel_right_unipotent adjacentRank_partialFourier_rowTranslate adjacentRank_rho0_kernel_right_orbit continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankContinuedForms equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound generalLinearDeterminantSlice hasCompactSupport_matrixSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelStarBaseBorel modelStarBaseDisconnected modelStarBaseGLBorel modelStarBaseGLMeasurable modelStarBaseLocalField modelStarBaseMeasurable modelStarBaseT2 modelStarBaseTopology modelStarBaseUnipotentBorel modelStarBaseUnipotentMeasurable modelStarBaseValuative modelStarFourierBorel modelStarFourierDisconnected modelStarFourierLocalField modelStarFourierMeasurable modelStarFourierT2 modelStarFourierTopology modelStarFourierValuative modelStarOrbitFourierBorel modelStarOrbitFourierDisconnected modelStarOrbitFourierLocalField modelStarOrbitFourierMeasurable modelStarOrbitFourierSecondCountable modelStarOrbitFourierT2 modelStarOrbitFourierTopology modelStarOrbitFourierValuative modelStarReductionBorel modelStarReductionDisconnected modelStarReductionGLBorel modelStarReductionGLMeasurable modelStarReductionLocalField modelStarReductionMeasurable modelStarReductionT2 modelStarReductionTopology modelStarReductionValuative modelStarRegularityLocalField modelStarRegularityTopology modelStarRegularityValuative normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding AdjacentRankUnipotentFourierStatement PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement adjacentRankUnipotentFourier padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicScalarHaarScaling padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.QuotientIntegration
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open scoped BigOperators

universe uF uV uG

private theorem biSmoothCoefficient_scalarAction
    {G : Type uG} [Group G] [TopologicalSpace G]
    {X : Type uV} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G X) (z : G) (c : ℂ)
    (hact : ∀ x, ρ z x = c • x)
    (f : GodementJacquet.biSmoothMatrixCoefficients ρ) :
    ∀ g, f.val (z * g) = c * f.val g := by
  have hf := f.property
  generalize hfa : f.val = a at hf ⊢
  clear hfa f
  induction hf using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨L, v, rfl⟩ := ha
    intro g
    change L.val (ρ (z * g) v.val) = c * L.val (ρ g v.val)
    rw [map_mul, Module.End.mul_apply, hact, map_smul]
    rfl
  | zero => intro g; simp
  | add a b ha hb iha ihb => intro g; simp [iha g, ihb g, mul_add]
  | smul a b hb ih => intro g; simp [ih g, mul_left_comm]

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance reflectionGroupMeasurable (r : ℕ) : MeasurableSpace
    (GeneralLinear (r + 1) F) := borel _
local instance reflectionGroupBorel (r : ℕ) : BorelSpace
    (GeneralLinear (r + 1) F) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))

attribute [local irreducible] coefficientModel modelRepresentation
  GodementJacquet.biSmoothMatrixCoefficients

/-- The scalar from reflecting the dual square test for the inverse
determinant twist of an actual model coefficient. -/
def adjacentRankDualMatrixReflectionScalar
    (χ : Quasicharacter F) (r : ℕ) (ζ : ℂˣ) : ℂˣ :=
  χ⁻¹ (determinant (-1 : GeneralLinear (r + 1) F)) * ζ

/-- Scalar action on the actual coefficient image gives the same scalar
on every actual bi-smooth coefficient of its right-translation action. -/
theorem biSmoothModelCoefficient_minusOne {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (ℓ : glFunctionals ψ r τ) (ζ : ℂˣ)
    (hζ : HasModelMinusOneScalar τ ℓ ζ)
    (f : GodementJacquet.biSmoothMatrixCoefficients
      (V := (glCoefficientModel ψ r τ ℓ).toSubmodule)
      (glModelRepresentation ψ r τ ℓ)) :
    ∀ g, f.val ((-1) * g) = (ζ : ℂ) * f.val g := by
  have hact (W : (glCoefficientModel ψ r τ ℓ).toSubmodule) :
      glModelRepresentation ψ r τ ℓ (-1) W = (ζ : ℂ) • W := by
    unfold glModelRepresentation modelRepresentation
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change W.val.val (g * (-1)) = (ζ : ℂ) * W.val.val g
    have hc : g * (-1) = (-1) * g := by apply Units.ext; simp
    rw [hc]
    exact hζ W g
  exact biSmoothCoefficient_scalarAction
    (G := GeneralLinear (r + 1) F)
    (X := (glCoefficientModel ψ r τ ℓ).toSubmodule)
    (glModelRepresentation ψ r τ ℓ) (-1) ζ hact f

private theorem inverseTranspose_minusOne {r : ℕ} :
    inverseTranspose (r + 1) F (-1) =
      (-1 : GeneralLinear (r + 1) F) := by
  apply Units.ext
  simp [inverseTranspose_coe]

/-- The actual inverse-transpose coefficient and inverse determinant
character have the indicated central reflection scalar. -/
theorem adjacentRankDualMatrixCoefficient_minusOne {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (ℓ : glFunctionals ψ r τ) (ζ : ℂˣ)
    (hζ : HasModelMinusOneScalar τ ℓ ζ)
    (χ : Quasicharacter F)
    (f : GodementJacquet.biSmoothMatrixCoefficients
      (V := (glCoefficientModel ψ r τ ℓ).toSubmodule)
      (glModelRepresentation ψ r τ ℓ))
    (g : GeneralLinear (r + 1) F) :
    (χ⁻¹ (determinant ((-1) * g)) : ℂ) *
        GodementJacquet.coefficientIota f.val ((-1) * g) =
      (adjacentRankDualMatrixReflectionScalar F χ r ζ : ℂ) *
        ((χ⁻¹ (determinant g) : ℂ) * GodementJacquet.coefficientIota f.val g) := by
  have hfi : GodementJacquet.coefficientIota f.val ((-1) * g) =
      (ζ : ℂ) * GodementJacquet.coefficientIota f.val g := by
    dsimp only [GodementJacquet.coefficientIota]
    rw [map_mul, inverseTranspose_minusOne F]
    exact biSmoothModelCoefficient_minusOne F ψ τ ℓ ζ hζ f _
  rw [hfi, map_mul, map_mul, Units.val_mul]
  simp only [adjacentRankDualMatrixReflectionScalar, Units.val_mul]
  ring

private theorem reflected_matrixIntegrand_mul_minusOne {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (v : GeneralLinear (r + 1) F → ℂ)
    (η : ℂˣ) (hv : ∀ g, v ((-1) * g) = (η : ℂ) * v g)
    (s : ℂ) (g : GeneralLinear (r + 1) F) :
    GodementJacquet.matrixIntegrand abv (adjacentRankReflectedTest Φ) s v ((-1) * g) =
      (η : ℂ) * GodementJacquet.matrixIntegrand abv Φ s v g := by
  have hw : determinantWeight abv (-1 : GeneralLinear (r + 1) F) s = 1 := by
    simp [determinantWeight, Units.val_neg, Units.val_one, Matrix.det_neg]
  simp only [GodementJacquet.matrixIntegrand, adjacentRankReflectedTest_apply,
    hv, determinantWeight_mul, hw, one_mul, Units.val_mul, Units.val_neg, Units.val_one,
    Matrix.neg_mul, neg_neg]
  ring

/-- Reflection preserves genuine matrix convergence, and the literal
matrix integral changes by exactly the supplied central scalar. -/
theorem adjacentRankMatrix_reflection {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (v : GeneralLinear (r + 1) F → ℂ)
    (η : ℂˣ) (hv : ∀ g, v ((-1) * g) = (η : ℂ) * v g) (s : ℂ) :
    (Langlands.AllField.GodementJacquet.Padic.MatrixConverges F (adjacentRankReflectedTest Φ) s v ↔
      Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ s v) ∧
    Langlands.AllField.GodementJacquet.Padic.matrixIntegral F (adjacentRankReflectedTest Φ) s v =
      (η : ℂ) * Langlands.AllField.GodementJacquet.Padic.matrixIntegral F Φ s v := by
  let μ := generalLinearHaar F r
  have hp := reflected_matrixIntegrand_mul_minusOne F Φ v η hv s
  have hfun : GodementJacquet.matrixIntegrand abv (adjacentRankReflectedTest Φ) s v ∘
      (fun g : GeneralLinear (r + 1) F => (-1) * g) =
      fun g => (η : ℂ) * GodementJacquet.matrixIntegrand abv Φ s v g := funext hp
  constructor
  · change Integrable _ μ ↔ Integrable _ μ
    rw [← (measurePreserving_mul_left μ (-1)).integrable_comp_emb
      (Homeomorph.mulLeft (-1 : GeneralLinear (r + 1) F)).measurableEmbedding,
      hfun]
    exact integrable_const_mul_iff η.isUnit _
  · change (∫ g, GodementJacquet.matrixIntegrand abv (adjacentRankReflectedTest Φ) s v g
      ∂μ) = (η : ℂ) * ∫ g, GodementJacquet.matrixIntegrand abv Φ s v g ∂μ
    rw [← integral_mul_left_eq_self
      (GodementJacquet.matrixIntegrand abv (adjacentRankReflectedTest Φ) s v) (-1)]
    simp_rw [hp]
    exact integral_const_mul _ _

/-- The actual shifted rational value of the reflected square test is the
constant scalar multiple of the original shifted rational value. -/
theorem adjacentRankMatrix_reflectedRationalValue {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (v : GeneralLinear (r + 1) F → ℂ)
    (η : ℂˣ) (hv : ∀ g, v ((-1) * g) = (η : ℂ) * v g)
    (M : RationalFunctions)
    (hM : GodementJacquet.HasShiftedRationalValue qF abv
      (generalLinearHaar F r) Φ v M) :
    GodementJacquet.HasShiftedRationalValue qF abv
      (generalLinearHaar F r) (adjacentRankReflectedTest Φ) v
      (RatFunc.C (η : ℂ) * M) := by
  constructor
  · obtain ⟨a, ha⟩ := hM.1
    exact ⟨a, fun s hs => (adjacentRankMatrix_reflection F Φ v η hv _).1.mpr (ha s hs)⟩
  · exact RationalContinuationLinear.continuation_of_eq_on_right
      (hasRationalContinuation_const_mul (η : ℂ) hM.2)
      ⟨0, fun s _ => (adjacentRankMatrix_reflection F Φ v η hv _).2⟩

private theorem scalar_minusOne {r : ℕ} :
    scalar (n := r + 1) (-1 : Fˣ) =
      (-1 : GeneralLinear (r + 1) F) := by
  apply Units.ext
  ext i j
  by_cases hij : i = j <;>
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Units.val_neg, Units.val_one, Matrix.neg_apply, hij]

/-- The model-star scalar and the square-test reflection leave precisely
the actual second model's minus-one scalar. -/
theorem adjacentRankModelStar_reflectionScalar_cancel
    (χ : Quasicharacter F) (r : ℕ) (ζ : ℂˣ) :
    adjacentRankModelStarScalar F χ r *
      (adjacentRankDualMatrixReflectionScalar F χ r ζ : ℂ) = (ζ : ℂ) := by
  have hs : χ⁻¹ (determinant (-1 : GeneralLinear (r + 1) F)) *
      χ⁻¹ (determinant (-1 : GeneralLinear (r + 1) F)) = 1 := by
    rw [← map_mul, ← map_mul]
    simp
  simp only [adjacentRankModelStarScalar, scalar_minusOne F,
    adjacentRankDualMatrixReflectionScalar, Units.val_mul]
  rw [← mul_assoc, ← Units.val_mul, hs, Units.val_one, one_mul]

/-- The same cancellation holds for the actual rational finite sum, so the
reflection scalar changes the equal-rank sign by exactly one power. -/
theorem adjacentRankModelStar_reflectedProduct_cancel
    (χ : Quasicharacter F) (r N : ℕ) (ζ : ℂˣ)
    (A M : Fin N → RationalFunctions) :
    RatFunc.C (adjacentRankModelStarScalar F χ r) *
        (∑ i, A i * (RatFunc.C
          (adjacentRankDualMatrixReflectionScalar F χ r ζ : ℂ) * M i)) =
      RatFunc.C (ζ : ℂ) * ∑ i, A i * M i := by
  have hc : RatFunc.C (adjacentRankModelStarScalar F χ r) *
      RatFunc.C (adjacentRankDualMatrixReflectionScalar F χ r ζ : ℂ) =
      RatFunc.C (ζ : ℂ) := by
    rw [← map_mul, adjacentRankModelStar_reflectionScalar_cancel]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (RatFunc.C (adjacentRankModelStarScalar F χ r) *
        RatFunc.C (adjacentRankDualMatrixReflectionScalar F χ r ζ : ℂ)) *
        (A i * M i) := by ring
    _ = _ := by rw [hc]

end Langlands.AllField.RankinSelberg.Padic
