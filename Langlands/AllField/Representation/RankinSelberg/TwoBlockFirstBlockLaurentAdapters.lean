import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentAdapters
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentIntegrands
/-!
# Adapters for the first-block Laurent assembly

The descended row character `[v] ↦ ψ((x v⁻¹)_0)` on the small quotient, joint
measurability of the fiber maps, and the vanishing of the two large integrands when
the test functional or the first block functional is zero.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
open Langlands.RankinSelberg.TwoBlockFirstBlockLaurent hiding aestronglyMeasurable_comp_fiberPoint_lowerRadical aestronglyMeasurable_firstRowCharacter coefficientModel_val_eq_zero continuous_firstRowCharacter dualIntegrand_reflectionQuotient firstBlockCoefficient firstBlockCoefficient_apply firstBlockCoefficient_lowerRadical_mul firstRowCharacter firstRowCharacter_mk inv_leviHalfModulus_blockPair_one lowerIntegrand_eq_zero_of_first lowerIntegrand_eq_zero_of_test lowerIntegrand_firstBlockFiberPoint measurePreserving_reflectionQuotient norm_firstRowCharacter partialSection_firstBlockEmbedding_mul reflectionQuotient_mem_determinantSlice scalarSection_eq_zero_of_first scalarSection_firstBlockEmbedding_mul scalarSection_lowerRadical_mul setIntegral_determinantSlice_reflectionQuotient tensorContraction_blockTensor_blockPair_one upperIntegrand_eq_zero_of_first upperIntegrand_eq_zero_of_test upperIntegrand_fiberPoint_rowSnoc whittaker_blockRotation_firstBlockEmbedding_lowerRadical
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul firstBlockAverage firstBlockAverage_mk isClopen_determinantSlice isClosed_mixedSubgroup measurableSet_determinantSlice mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mk_mem_determinantSlice normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicScalarHaarScaling padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.QuotientIntegration
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker

universe uF uW uV

variable {F : Type uF} [Field F]

section RowCharacter

variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F) (n : ℕ)

/-- The row character `[v] ↦ ψ((x v⁻¹)_0)` on `N \ GL_(n+1)`, by actual descent: right
multiplication of a row by an upper unipotent matrix does not change its first entry. -/
def firstRowCharacter (x : Fin (n + 1) → F) :
    LeftUnipotentQuotient n F → ℂ :=
  descend (upperUnipotent (n + 1) F)
    (fun v => ψ.complex (Matrix.vecMul x (v⁻¹).val 0))
    (fun u v => by
      change ψ.complex (Matrix.vecMul x ((u.val * v)⁻¹).val 0) =
        ψ.complex (Matrix.vecMul x (v⁻¹).val 0)
      rw [mul_inv_rev, Units.val_mul, ← Matrix.vecMul_vecMul]
      exact congrArg ψ.complex (TwoBlockLowerUnfolding.vecMul_upperUnipotent_zero _ u⁻¹))

@[simp]
theorem firstRowCharacter_mk (x : Fin (n + 1) → F)
    (v : GeneralLinear (n + 1) F) :
    firstRowCharacter ψ n x (Quotient.mk _ v) = ψ.complex (Matrix.vecMul x (v⁻¹).val 0) :=
  rfl

theorem norm_firstRowCharacter (x : Fin (n + 1) → F)
    (q : LeftUnipotentQuotient n F) :
    ‖firstRowCharacter ψ n x q‖ = 1 := by
  induction q using Quotient.inductionOn with
  | h v => exact ψ.norm_complex _

theorem continuous_firstRowCharacter :
    Continuous (fun p : (Fin (n + 1) → F) × LeftUnipotentQuotient n F =>
      firstRowCharacter ψ n p.1 p.2) := by
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (n + 1)
  have hq : Topology.IsQuotientMap (Prod.map (id : (Fin (n + 1) → F) → _)
      (leftQuotientMap (upperUnipotent (n + 1) F))) :=
    (IsOpenQuotientMap.id.prodMap (leftQuotient_isOpenQuotientMap _)).isQuotientMap
  refine hq.continuous_iff.mpr ?_
  change Continuous (fun p : (Fin (n + 1) → F) × GeneralLinear (n + 1) F =>
    ψ.complex (Matrix.vecMul p.1 (p.2⁻¹).val 0))
  refine ψ.continuous_complex.comp ?_
  have hinv : Continuous fun g : GeneralLinear (n + 1) F => (g⁻¹).val :=
    Units.continuous_coe_inv
  exact (continuous_apply 0).comp
    (Continuous.matrix_vecMul continuous_fst (hinv.comp continuous_snd))

/-- Joint almost-everywhere strong measurability of the row character for every measure
on the product of rows and the Borel small quotient. -/
theorem aestronglyMeasurable_firstRowCharacter :
    letI : MeasurableSpace F := borel F
    letI : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
    ∀ ρ : Measure ((Fin (n + 1) → F) × LeftUnipotentQuotient n F),
      AEStronglyMeasurable (Function.uncurry (firstRowCharacter ψ n)) ρ := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  have := T.secondCountableTopology
  have := T.generalLinearSecondCountableTopology (n + 1)
  let := T.generalLinearTopologicalGroup (n + 1)
  have : SecondCountableTopology (LeftUnipotentQuotient n F) :=
    Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)
  intro ρ
  exact (continuous_firstRowCharacter ψ n).aestronglyMeasurable

end RowCharacter

section FiberMeasurability

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- Joint almost-everywhere strong measurability of `(Z, q) ↦ E([diag(v_q, 1) R(Z) g])`
for continuous `E`. -/
theorem aestronglyMeasurable_comp_fiberPoint_lowerRadical [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (E : TwoBlockUnipotentQuotient.BlockQuotient h F → ℂ)
    (g : GeneralLinear (t + 1) F) :
    letI : MeasurableSpace F := borel F
    letI : MeasurableSpace (LeftUnipotentQuotient (m 0) F) := borel _
    Continuous E →
    ∀ ρ : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F ×
        LeftUnipotentQuotient (m 0) F),
      AEStronglyMeasurable (Function.uncurry fun Z x =>
        E (fiberPoint h F x (lowerRadical h F Z * g))) ρ := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient (m 0) F) := borel _
  let : BorelSpace (LeftUnipotentQuotient (m 0) F) := ⟨rfl⟩
  have := T.secondCountableTopology
  have := T.generalLinearSecondCountableTopology (m 0 + 1)
  let := T.generalLinearTopologicalGroup (m 0 + 1)
  let := T.generalLinearTopologicalGroup (t + 1)
  have : SecondCountableTopology (LeftUnipotentQuotient (m 0) F) :=
    Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)
  have : SecondCountableTopology (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F) :=
    inferInstanceAs (SecondCountableTopology (Fin (m 1 + 1) → Fin (m 0 + 1) → F))
  have : OpensMeasurableSpace (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F) :=
    inferInstanceAs (OpensMeasurableSpace (Fin (m 1 + 1) → Fin (m 0 + 1) → F))
  intro hE ρ
  have hc : Continuous (fun p : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F ×
      LeftUnipotentQuotient (m 0) F =>
      E (fiberPoint h F p.2 (lowerRadical h F p.1 * g))) :=
    hE.comp ((continuous_fiberPoint F h).comp (continuous_snd.prodMk
      (((TwoBlockLowerFirstBlockQuotient.continuous_lowerRadical h F).comp continuous_fst).mul continuous_const)))
  exact hc.aestronglyMeasurable

end FiberMeasurability

section Degenerate

variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}

/-- A zero first functional makes every scalar section vanish. -/
theorem scalarSection_eq_zero_of_first [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (ell : ∀ i, W i →ₗ[ℂ] ℂ) (h0 : ell 0 = 0)
    (f : Sections F h σ) (g : GeneralLinear (t + 1) F)
    (a : (succBlockShape m h).Levi F) : scalarSection ell f g a = 0 := by
  rw [scalarSection_def]
  generalize (succBlockShape m h).blockTensor σ a (sectionEval F h σ f g) = X
  induction X using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    rw [map_smul, tensorContraction_tprod, Fin.prod_univ_two, h0, LinearMap.zero_apply,
      zero_mul, smul_zero]
  | add x y hx hy => rw [map_add, hx, hy, add_zero]

variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F}

/-- The upper integrand vanishes for a zero first functional. -/
theorem upperIntegrand_eq_zero_of_first
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)) (h0 : (ell 0).val = 0)
    (f : Sections F h σ)
    (Wtest : RankinSelberg.WhittakerFunctions ψ t)
    (Φ : SchwartzBruhat (Fin (t + 1) → F)) :
    Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand ell f Wtest Φ = 0 := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    rw [Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand_mk, scalarSection_eq_zero_of_first _ h0, mul_zero, zero_mul]
    rfl

/-- The upper integrand vanishes for a zero test function. -/
theorem upperIntegrand_eq_zero_of_test
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ)
    (Wtest : RankinSelberg.WhittakerFunctions ψ t) (hW : Wtest.val = 0)
    (Φ : SchwartzBruhat (Fin (t + 1) → F)) :
    Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand ell f Wtest Φ = 0 := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    rw [Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand_mk, hW, Pi.zero_apply, zero_mul, zero_mul]
    rfl

/-- The lower integrand vanishes for a zero first functional. -/
theorem lowerIntegrand_eq_zero_of_first [MeasurableSpace F]
    [@BorelSpace F (⟨⟩ : LocalFieldData F).topology _]
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)) (h0 : (ell 0).val = 0)
    (f : Sections F h σ)
    (Wtest : RankinSelberg.WhittakerFunctions ψ t)
    (Φ : SchwartzBruhat (Fin (t + 1) → F))
    (μ : AdditiveHaarMeasure F) :
    Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.integrand ell f Wtest Φ μ = 0 := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    rw [Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.integrand_mk, scalarSection_eq_zero_of_first _ h0, mul_zero,
      zero_mul]
    rfl

/-- The lower integrand vanishes for a zero test function. -/
theorem lowerIntegrand_eq_zero_of_test [MeasurableSpace F]
    [@BorelSpace F (⟨⟩ : LocalFieldData F).topology _]
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ)
    (Wtest : RankinSelberg.WhittakerFunctions ψ t) (hW : Wtest.val = 0)
    (Φ : SchwartzBruhat (Fin (t + 1) → F))
    (μ : AdditiveHaarMeasure F) :
    Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.integrand ell f Wtest Φ μ = 0 := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    rw [Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.integrand_mk, hW, Pi.zero_apply, zero_mul, zero_mul]
    rfl

/-- Every vector of the coefficient image of a zero functional is the zero function. -/
theorem coefficientModel_val_eq_zero {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GeneralLinear (t + 1) F) V}
    {lambda : glFunctionals ψ t π}
    (hlam : lambda.val = 0)
    (Wtest : (coefficientModel π lambda).toSubmodule) :
    Wtest.val.val = 0 := by
  obtain ⟨v, hv⟩ := Wtest.property
  rw [← hv]
  funext g
  change lambda.val (π g v) = 0
  rw [hlam, LinearMap.zero_apply]

end Degenerate

end Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
