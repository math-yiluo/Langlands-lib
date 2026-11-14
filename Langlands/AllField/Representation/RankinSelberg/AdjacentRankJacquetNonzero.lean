import Langlands.Representation.RankinSelberg.AdjacentRankJacquetNonzero
import Langlands.AllField.Group.GL.BlockIwahoriBasis
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankJacquetCovariance
/-! Nonvanishing of the actual adjacent Jacquet functional by a compact local section. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Topology Matrix

namespace Langlands.AllField.RankinSelberg.AdjacentJacquet
open Langlands.RankinSelberg.AdjacentJacquet hiding determinantWeight_eq exists_constantKernel_section functional functional_coefficient functional_ne_zero inducedRepresentation inducing_isSmooth integrable_normalizedSection_realTwist integral integralLinear integralLinear_apply integralLinear_coefficient integral_normalizedSection_eq_doubleIntegral integral_normalizedSection_eq_modelIntegral integral_right integral_unipotent_mul integrand integrandLinear integrandLinear_apply integrand_normalizedSection integrand_right integrand_unipotent_mul jacquetCovarianceBorel jacquetCovarianceLocalField jacquetCovarianceMeasurable jacquetCovarianceSecondCountable jacquetCovarianceSigmaCompact jacquetCovarianceTopology jacquetCovarianceValuativeRel jacquetEvaluationBorel jacquetEvaluationGLBorel jacquetEvaluationGLLocallyCompact jacquetEvaluationGLMeasurable jacquetEvaluationGLSecondCountable jacquetEvaluationLocalField jacquetEvaluationMeasurable jacquetEvaluationNonarchRing jacquetEvaluationT2 jacquetEvaluationTopology jacquetEvaluationValuativeRel jacquetLinearMeasurable jacquetLinearTopology jacquetNonzeroBorel jacquetNonzeroLocalField jacquetNonzeroMeasurable jacquetNonzeroNonarchRing jacquetNonzeroSecondCountable jacquetNonzeroSigmaCompact jacquetNonzeroTopology jacquetNonzeroValuativeRel measurableEmbedding_unipotentShift measurePreserving_unipotentShift phase_eq_one_neighborhood sectionCoefficient sectionCoefficientLinear sectionCoefficientLinear_apply sectionCoefficient_lowerBlock sectionCoefficient_normalizedSection sectionCoefficient_right tensorCoordinates_lowerBlock_action
open Langlands.AllField.RankinSelberg.AdjacentJacquet
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneWhittakerTypeStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement adjacentRankDeterminantWeight adjacentRankDeterminantWeight_apply adjacentRankDeterminantWeight_locallyConstant adjacentRankLowerScalarProjection adjacentRankLower_determinantComplexPower adjacentRankLower_halfModulus adjacentRankLower_weightRatio adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic functionalsCongr hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker hiding unipotentShift

universe uF uV

section Algebra




end Algebra

section Padic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance jacquetNonzeroT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance jacquetNonzeroSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance jacquetNonzeroSigmaCompact : SigmaCompactSpace F :=
  (⟨⟩ : LocalFieldData F).sigmaCompactSpace
local instance jacquetNonzeroNonarchRing : NonarchimedeanRing F := by
  convert! ValuativeRel.nonarchimedeanRing F
  exact Valuation.toTopologicalSpace_eq _
local instance jacquetNonzeroMeasurable : MeasurableSpace F := borel _
local instance jacquetNonzeroBorel : BorelSpace F := ⟨rfl⟩

variable (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
  (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F)

include ψ in
/-- The exact normalized tensor-valued inducing action is smooth. -/
theorem inducing_isSmooth (hσ : IsSmooth σ) :
    IsSmooth (Langlands.AllField.RankinSelberg.Padic.adjacentRankLowerTensorRepresentation F σ χ) := by
  have hf : ∀ i : Fin 2,
      IsSmooth (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ) i) := by
    intro i
    fin_cases i
    · exact hσ
    · exact rankOneExtensionCharacter_isSmooth F ψ χ
  exact (isSmooth_twist_iff _ _
    ((⟨⟩ : LocalFieldData F).isOpen_ker_oppositeParabolicHalfModulus
      (adjacentRankLowerShape r))).2
    (isSmooth_comp _ ((⟨⟩ : LocalFieldData F).oppositeBlockLeviProjection
      (adjacentRankLowerShape r)).continuous (FiniteTensor.isSmooth_external _ hf))

/-- The negative Jacquet phase is trivial on an open neighborhood of zero. -/
theorem phase_eq_one_neighborhood :
    ∃ O : Set (Fin (r + 1) → F), IsOpen O ∧ 0 ∈ O ∧
      ∀ x ∈ O, ψ.complex (-x (Fin.last r)) = 1 := by
  have : NonarchimedeanGroup (Multiplicative F) :=
    { is_nonarchimedean := by
        intro U hU
        obtain ⟨H, hH⟩ := NonarchimedeanAddGroup.is_nonarchimedean
          (Multiplicative.ofAdd ⁻¹' U) hU
        exact ⟨{
          toSubgroup := {
            carrier := {x | x.toAdd ∈ H}
            one_mem' := H.zero_mem
            mul_mem' := H.add_mem
            inv_mem' := H.neg_mem
          }
          isOpen' := H.isOpen
        }, hH⟩ }
  let θ : Multiplicative F →* ℂˣ :=
    Circle.toUnits.comp ψ.toAddChar.toMonoidHom
  have hθ : Continuous θ := by
    apply Units.continuous_iff.mpr
    constructor
    · exact ψ.continuous_complex
    · change Continuous (fun x : F => (ψ.complex x)⁻¹)
      have hc : Continuous (fun x : F => ψ.complex (-x)) :=
        ψ.continuous_complex.comp continuous_neg
      simpa only [AddChar.map_neg_eq_inv] using hc
  have hker := isOpen_ker_of_continuous_complex_character θ hθ
  let O : Set (Fin (r + 1) → F) :=
    (fun x => Multiplicative.ofAdd (-x (Fin.last r))) ⁻¹' (θ.ker : Set _)
  refine ⟨O, hker.preimage ((continuous_apply (A := fun _ : Fin (r + 1) => F) (Fin.last r)).neg :
    Continuous fun x : Fin (r + 1) → F => Multiplicative.ofAdd (-x (Fin.last r))), ?_, ?_⟩
  · change θ (Multiplicative.ofAdd (-(0 : Fin (r + 1) → F) (Fin.last r))) = 1
    simp
  · intro x hx
    exact congrArg Units.val hx

/-- A compact local section has the prescribed constant kernel near zero,
with the phase killed on its full cell support. -/
theorem exists_constantKernel_section (hσ : IsSmooth σ) (v : V) :
    ∃ (L : Set (Fin (r + 1) → F))
      (f : (inducedRepresentation F σ χ).asModule),
      IsOpen L ∧ IsCompact L ∧ 0 ∈ L ∧
      integrand F ψ σ ℓ χ f 1 = L.indicator (fun _ => ℓ.val v) := by
  classical
  let T := (⟨⟩ : LocalFieldData F)
  let := T.generalLinearTopologicalGroup (r + 2)
  let B := adjacentRankLowerShape r
  let P := B.oppositeParabolic F
  let G := GeneralLinear (r + 2) F
  let τ := Langlands.AllField.RankinSelberg.Padic.adjacentRankLowerTensorRepresentation F σ χ
  let z := (adjacentRankLowerTensorCoordinates V).symm v
  obtain ⟨O, hO, hO0, hphase⟩ := phase_eq_one_neighborhood F ψ (r := r)
  obtain ⟨H, hH⟩ := inducing_isSmooth F ψ σ χ hσ z
  obtain ⟨O', hO'open, hO'⟩ := isOpen_induced_iff.mp H.isOpen
  let U : Set G := O' ∩ columnCoordinate ⁻¹' O
  have hU : U ∈ 𝓝 (1 : G) := by
    refine IsOpen.mem_nhds (hO'open.inter (hO.preimage continuous_columnCoordinate)) ?_
    constructor
    · have h1 : (1 : P) ∈ (Subtype.val ⁻¹' O' : Set P) := by
        rw [hO']
        exact H.one_mem
      exact h1
    · change columnCoordinate (1 : G) ∈ O
      rw [← upperColumn_zero, columnCoordinate_upperColumn]
      exact hO0
  obtain ⟨K, hKc, hKU, hKfac⟩ :=
    (Langlands.AllField.GeneralLinear.BlockShape.exists_compactOpenSubgroup_hasBlockIwahoriFactorization B) T hU
  have hfac : ∀ g ∈ K, ∃ q ∈ P, ∃ n ∈ K,
      n ∈ B.unipotentSubgroup F ∧ g = q * n := by
    intro g hg
    obtain ⟨⟨l, m, n⟩, hlmn⟩ :=
      (Langlands.AllField.GeneralLinear.BlockShape.HasBlockIwahoriFactorization.bijective _ _ hKfac).2 ⟨g, hg⟩
    have he : l.val * m.val * n.val = g := congrArg Subtype.val hlmn
    exact ⟨l.val * m.val,
      P.mul_mem (B.oppositeUnipotentSubgroup_le_oppositeParabolic F l.property.2)
        (B.leviSubgroup_le_oppositeParabolic F m.property.2),
      n.val, n.property.1, n.property.2, he.symm⟩
  let L : Set (Fin (r + 1) → F) := upperColumn ⁻¹' (K : Set G)
  have hLopen : IsOpen L := K.isOpen.preimage continuous_upperColumn
  have hLclosed : IsClosed L := K.isClosed.preimage continuous_upperColumn
  have hL0 : (0 : Fin (r + 1) → F) ∈ L := by
    change upperColumn 0 ∈ K
    rw [upperColumn_zero]
    exact K.one_mem
  have hLsub : L ⊆ columnCoordinate '' (K : Set G) :=
    fun x hx => ⟨upperColumn x, hx, columnCoordinate_upperColumn x⟩
  have hLcompact : IsCompact L :=
    (hKc.image continuous_columnCoordinate).of_isClosed_subset hLclosed hLsub
  have hLO : L ⊆ O := by
    intro x hx
    have h := (hKU hx).2
    change columnCoordinate (upperColumn x) ∈ O at h
    rwa [columnCoordinate_upperColumn] at h
  have hz : z ∈ fixedVectors τ (Induction.conjOpenSubgroup P K 1).toSubgroup := by
    rintro ⟨q, hq⟩
    have hqK : (q : G) ∈ K := by
      simpa using Induction.mem_conjOpenSubgroup.mp hq
    have hqH : q ∈ H := by
      have h1 : q ∈ (Subtype.val ⁻¹' O' : Set P) := (hKU hqK).1
      rw [hO'] at h1
      exact h1
    exact hH ⟨q, hqH⟩
  let s := Induction.compactDoubleCosetSection P τ K hKc 1 z hz
  have key : ∀ g : G, Induction.eval P τ s.val g ≠ 0 →
      ∃ q ∈ P, ∃ n ∈ K, n ∈ B.unipotentSubgroup F ∧ g = q * n := by
    intro g hg
    have hmem : Induction.quotientMap P g ∈
        Induction.quotientSupport P (Induction.eval P τ s.val) := ⟨g, hg, rfl⟩
    obtain ⟨k, hk, hkk⟩ :=
      Induction.compactDoubleCosetSection_support_subset P τ K hKc 1 z hz hmem
    have hr : g * (1 * k)⁻¹ ∈ P := QuotientGroup.rightRel_apply.mp (Quotient.exact hkk)
    obtain ⟨q₀, hq₀, n, hnK, hnN, hkeq⟩ := hfac k hk
    refine ⟨g * k⁻¹ * q₀, P.mul_mem (by simpa using hr) hq₀, n, hnK, hnN, ?_⟩
    subst hkeq
    group
  have hcell : ∀ x, x ∉ L → Induction.eval P τ s.val (upperColumn x) = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨q, hq, n, hnK, hnN, he⟩ := key _ hne
    have hqN : q ∈ B.unipotentSubgroup F := by
      have hqeq : q = upperColumn x * n⁻¹ := by
        rw [he]
        group
      rw [hqeq]
      exact (B.unipotentSubgroup F).mul_mem (upperColumn_mem_radical x)
        ((B.unipotentSubgroup F).inv_mem hnN)
    have hq1 := B.eq_one_of_mem_oppositeParabolic_of_mem_unipotentSubgroup
      F hq hqN
    apply hx
    change upperColumn x ∈ K
    rw [he, hq1, one_mul]
    exact hnK
  refine ⟨L, s.val, hLopen, hLcompact, hL0, ?_⟩
  funext x
  change ℓ.val (adjacentRankLowerTensorCoordinates V
      (Induction.eval P τ s.val (upperColumn x * 1))) *
    ψ.complex (-x (Fin.last r)) = L.indicator (fun _ => ℓ.val v) x
  rw [mul_one]
  by_cases hx : x ∈ L
  · have hs := Induction.compactDoubleCosetSection_apply P τ K hKc 1 z hz 1
      ⟨upperColumn x, hx⟩
    simp only [OneMemClass.coe_one, one_mul, map_one] at hs
    rw [hs, hphase x (hLO hx), mul_one, Set.indicator_of_mem hx]
    exact congrArg ℓ.val ((adjacentRankLowerTensorCoordinates V).apply_symm_apply v)
  · rw [hcell x hx, map_zero, map_zero, zero_mul, Set.indicator_of_notMem hx]

/-- For any base character and supplied Haar, the actual Jacquet functional
is nonzero whenever its all-section convergence premise holds. -/
theorem functional_ne_zero (ν : AdditiveHaarMeasure F)
    (hσ : IsSmooth σ) (hℓ : ℓ.val ≠ 0)
    (hI : ∀ (f : (inducedRepresentation F σ χ).asModule)
      (g : GeneralLinear (r + 2) F),
      Integrable (integrand F ψ σ ℓ χ f g) (rowMeasure ν (r + 1))) :
    (functional F ψ σ ℓ χ ν hI).val ≠ 0 := by
  classical
  have hex : ∃ v, ℓ.val v ≠ 0 := by
    by_contra h
    apply hℓ
    ext v
    exact not_not.mp (not_exists.mp h v)
  obtain ⟨v, hv⟩ := hex
  obtain ⟨L, f, hLo, hLc, hL0, hf⟩ :=
    exists_constantKernel_section F ψ σ ℓ χ hσ v
  let μ := rowMeasure ν (r + 1)
  have hpos : 0 < μ L := hLo.measure_pos μ ⟨0, hL0⟩
  have hfin : μ L < ⊤ := hLc.measure_lt_top
  have hreal : 0 < μ.real L := ENNReal.toReal_pos hpos.ne' hfin.ne
  have hval : (functional F ψ σ ℓ χ ν hI).val f =
      (μ.real L : ℂ) * ℓ.val v := by
    change (∫ x, integrand F ψ σ ℓ χ f 1 x ∂μ) = _
    rw [hf, integral_indicator_const _ hLo.measurableSet, Complex.real_smul]
  intro hzero
  have hne : (μ.real L : ℂ) * ℓ.val v ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hreal.ne') hv
  apply hne
  rw [← hval, hzero, LinearMap.zero_apply]

end Padic

end Langlands.AllField.RankinSelberg.AdjacentJacquet
