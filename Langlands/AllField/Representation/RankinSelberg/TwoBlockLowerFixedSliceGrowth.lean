import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceGrowth
import Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergenceProof
/-!
# Growth bounds for the Section 4.7 lower quotient

The standard-character test coefficient has a uniform geometric growth base.
Block section bounds follow from finite compact images and the exact opposite twist.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
open Langlands.RankinSelberg.TwoBlockLowerFixedSlice hiding exists_coefficient_growth exists_coefficient_torusSize_growth exists_coefficient_torus_growth exists_section_growth exists_standard_functional_growth instIsNonarchimedeanLocalFieldCarrier instTopologicalSpaceCarrier instValuativeRelCarrier isEntryBounded_torus
open Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement determinantComplexPower_upperUnipotent isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockDeformation hiding blockTensor_twoBlockDeformedBlocks blockZeroNorm blockZeroNorm_mul_integral blockZeroNorm_oppositeParabolic_mul blockZeroNorm_pos compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent determinantNorm_oppositeLeviProjection_of_mem exists_oppositeParabolic_mul exists_uniform_stabilizer flatFunction flatFunction_covariant flatFunction_mul_flatStabilizer flatSection flatSection_zero flatStabilizer flatStabilizer_le_integralOpen inducedRep_mem_compactRadicalSubmodule integralOpen integral_comp_unipotentShift inverseStandardCharacter_eq_prod inverseTranspose_mem_integralOpen isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule isCompact_integralOpen isLocallyConstant_blockZeroNorm isLocallyConstant_oppositeBlockNorm jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule mem_integralOpen mem_oppositeParabolic_of_lower oppositeBlockNorm oppositeBlockNorm_eq oppositeBlockNorm_mul_integral oppositeBlockNorm_oppositeParabolic_mul oppositeBlockNorm_pos radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul sectionEval_mul_flatStabilizer tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockConvergence hiding box boxFieldLocalField boxFieldTopology boxFieldValuativeRel box_eq_pi exists_blockTensor_growth exists_bound_isAbsIntegrable_of_factorization exists_functional_growth exists_integral_growth exists_radical_factorization finite_image_sectionEval_integralOpen integrable_integrand_one measurableSet_box measure_preimage_uniformizer_pow_mul norm_integrand_le norm_inv_leviHalfModulus_le_one normalizedAbs_determinant_eq_one proofFieldBorelSpace proofFieldLocalField proofFieldMeasurableSpace proofFieldTopology proofFieldValuativeRel radicalFieldValuativeRel rectangularMeasure_box residue_pow_rpow_neg tensorContraction_blockTensor_twist uniformizerUnit_isUniformizingElement
open Langlands.AllField.RankinSelberg.TwoBlockConvergence

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

/-- The standard-character counterpart of the inverse-functional growth estimate.
The base depends on the representation and functional, before the vector. -/
theorem exists_standard_functional_growth (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
    (hρ : IsOfWhittakerType n (standardCharacter ψ n) ρ) (ℓ : glFunctionals ψ n ρ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ v : V, ∃ C : ℝ, ∀ (e : ℕ) (g : GeneralLinear (n + 1) F),
      IsEntryBounded (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) e g →
        ‖ℓ.val (ρ g v)‖ ≤ C * B ^ e := by
  set T := (⟨⟩ : LocalFieldData F)
  have hϖ := uniformizerUnit_isUniformizingElement F
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : F, ψ x₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact ψ.nontrivial (AddChar.ext _ _ hcon)
  have hχ₀ : ψ.complex x₀ ≠ 1 := by
    rw [ne_eq, UnitaryAdditiveCharacter.complex_apply, Circle.coe_eq_one]
    exact hx₀
  obtain ⟨c₀, hc₀⟩ := exists_pow_mul_mem_integer hϖ x₀
  obtain ⟨n₀, hn₀⟩ := T.exists_additiveTrivialAt ψ
  refine exists_growth ρ hρ.1 hρ.2.1 ℓ.val ψ.complex
    (fun x hx v => ℓ.property ⟨x, hx⟩ v)
    (fun z => ψ.norm_complex z) hϖ hχ₀ hc₀ (a₀ := (-n₀).toNat)
    fun z hz => ?_
  have hz1 : ψ z = 1 := by
    refine hn₀ z ?_
    rw [T.mem_additiveLattice_iff_div_mem_integers,
      ← Langlands.LocalFactor.LocalAbelian.uniformizerUnit_coe T]
    have hpos := Iwasawa.valuation_pos (ValuativeRel.valuation F)
      (Langlands.LocalFactor.LocalAbelian.uniformizerUnit T)
    have hle := valuation_le_of_mem_levelSet hϖ hz
    change ValuativeRel.valuation F
      (z / (Langlands.LocalFactor.LocalAbelian.uniformizerUnit T : F) ^ (-n₀)) ≤ 1
    rw [map_div₀, map_zpow₀, zpow_neg, div_inv_eq_mul]
    have hn : 0 ≤ ((-n₀).toNat : ℤ) + n₀ := by
      have := Int.self_le_toNat (-n₀)
      omega
    calc
      ValuativeRel.valuation F z *
          ValuativeRel.valuation F
            (Langlands.LocalFactor.LocalAbelian.uniformizerUnit T : F) ^ n₀ ≤
          ValuativeRel.valuation F
              (Langlands.LocalFactor.LocalAbelian.uniformizerUnit T : F) ^ (-n₀).toNat *
            ValuativeRel.valuation F
              (Langlands.LocalFactor.LocalAbelian.uniformizerUnit T : F) ^ n₀ :=
        by gcongr
      _ = ValuativeRel.valuation F
            (Langlands.LocalFactor.LocalAbelian.uniformizerUnit T : F) ^
              (((-n₀).toNat : ℤ) + n₀) := by
        rw [zpow_add₀ hpos.ne', zpow_natCast]
      _ ≤ 1 := (zpow_le_one_iff_right_of_lt_one₀ hpos hϖ.1).mpr hn
  rw [UnitaryAdditiveCharacter.complex_apply, hz1, Circle.coe_one]

/-- Every actual coefficient-image vector inherits the same growth base. -/
theorem exists_coefficient_growth (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (n + 1) F) V)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π) (ell : glFunctionals ψ n π) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ W : (coefficientModel π ell).toSubmodule,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (e : ℕ) (g : GeneralLinear (n + 1) F),
        IsEntryBounded (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) e g →
          ‖W.val.val g‖ ≤ C * B ^ e := by
  obtain ⟨B, hB, hgrowth⟩ := exists_standard_functional_growth F ψ π hπ ell
  refine ⟨B, hB, fun W => ?_⟩
  obtain ⟨v, hv⟩ := modelMap_surjective π ell W
  obtain ⟨C, hC⟩ := hgrowth v
  refine ⟨max C 0, le_max_right _ _, fun e g hg => ?_⟩
  have hW : W.val.val g = ell.val (π g v) := by
    rw [← hv]
    rfl
  rw [hW]
  exact (hC e g hg).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (zero_le_one.trans hB) e))

/-- A diagonal uniformizer matrix is entry-bounded by any common bound for
its positive and negative exponents. -/
theorem isEntryBounded_torus {n : ℕ} {ϖ : Fˣ}
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ)
    (lam : Fin n → ℤ) (e : ℕ) (he : ∀ i, -(e : ℤ) ≤ lam i ∧ lam i ≤ e) :
    IsEntryBounded ϖ e (Iwasawa.torus ϖ lam) := by
  have hpow (z : ℤ) :
      (ϖ : F) ^ e * ((ϖ ^ z : Fˣ) : F) =
        ((ϖ ^ ((e : ℤ) + z) : Fˣ) : F) := by
    rw [zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]
  intro i j
  by_cases hij : i = j
  · subst j
    constructor
    · change (ϖ : F) ^ e *
        (Iwasawa.torus ϖ lam).val i i ∈ (ValuativeRel.valuation F).integer
      rw [Iwasawa.torus_val, Matrix.diagonal_apply_eq, hpow]
      exact zpow_mem_integer_of_nonneg hϖ.1.le (by have := (he i).1; omega)
    · change (ϖ : F) ^ e *
        (Iwasawa.torus ϖ lam)⁻¹.val i i ∈ (ValuativeRel.valuation F).integer
      rw [Iwasawa.torus_inv_val, Matrix.diagonal_apply_eq, ← zpow_neg, hpow]
      exact zpow_mem_integer_of_nonneg hϖ.1.le (by have := (he i).2; omega)
  · constructor
    · change (ϖ : F) ^ e *
        (Iwasawa.torus ϖ lam).val i j ∈ (ValuativeRel.valuation F).integer
      rw [Iwasawa.torus_val, Matrix.diagonal_apply_ne _ hij, mul_zero]
      exact zero_mem _
    · change (ϖ : F) ^ e *
        (Iwasawa.torus ϖ lam)⁻¹.val i j ∈ (ValuativeRel.valuation F).integer
      rw [Iwasawa.torus_inv_val, Matrix.diagonal_apply_ne _ hij, mul_zero]
      exact zero_mem _

/-- Uniform growth of actual test coefficients on diagonal/compact coordinates,
including any fixed left translate such as the block rotation. -/
theorem exists_coefficient_torus_growth (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (n + 1) F) V)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π) (ell : glFunctionals ψ n π) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ W : (coefficientModel π ell).toSubmodule,
      ∀ c : GeneralLinear (n + 1) F, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (lam : Fin (n + 1) → ℤ) (e : ℕ),
        (∀ i, -(e : ℤ) ≤ lam i ∧ lam i ≤ e) →
        ∀ k ∈ integralOpen F n,
          ‖W.val.val (c * Iwasawa.torus
            (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) lam * k)‖ ≤
              C * B ^ e := by
  obtain ⟨B, hB, hgrowth⟩ := exists_coefficient_growth F ψ π hπ ell
  refine ⟨B, hB, fun W c => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hgrowth W
  have hϖ := uniformizerUnit_isUniformizingElement F
  obtain ⟨ec, hec⟩ := exists_isEntryBounded hϖ c
  refine ⟨C * B ^ ec, mul_nonneg hC0 (pow_nonneg (zero_le_one.trans hB) _),
    fun lam e he k hk => ?_⟩
  have hk' := (mem_integralOpen F k).1 hk
  have hkbounded : IsEntryBounded
      (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) 0 k := by
    intro i j
    simpa only [pow_zero, one_mul] using And.intro (hk'.1 i j) (hk'.2 i j)
  have hbounded := (hec.mul (isEntryBounded_torus F hϖ lam e he)).mul hkbounded
  rw [add_zero] at hbounded
  calc
    _ ≤ C * B ^ (ec + e) := hC _ _ hbounded
    _ = _ := by rw [pow_add]; ring

/-- The same coefficient bound with the canonical integral `l¹` size. -/
theorem exists_coefficient_torusSize_growth (ψ : UnitaryAdditiveCharacter F)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (n + 1) F) V)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π) (ell : glFunctionals ψ n π) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ W : (coefficientModel π ell).toSubmodule,
      ∀ c : GeneralLinear (n + 1) F, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (lam : Fin (n + 1) → ℤ) (k : GeneralLinear (n + 1) F),
        k ∈ integralOpen F n →
          ‖W.val.val (c * Iwasawa.torus
            (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) lam * k)‖ ≤
              C * B ^ torusSize lam := by
  obtain ⟨B, hB, hgrowth⟩ := exists_coefficient_torus_growth F ψ π hπ ell
  refine ⟨B, hB, fun W c => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hgrowth W c
  exact ⟨C, hC0, fun lam k hk => hC lam (torusSize lam) (torusSize_bounds lam) k hk⟩

section Sections

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- Uniform block-section growth, with the inverse upper half modulus and both
opposite twists displayed exactly. The growth base precedes the twist and section. -/
theorem exists_section_growth (ψ : UnitaryAdditiveCharacter F)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i)) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (u : ℝ)
      (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u)),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ k ∈ integralOpen F t, ∀ (e : ℕ)
        (b : (succBlockShape m h).Levi F),
        (∀ i, IsEntryBounded
          (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) e (b i)) →
        ‖scalarSection (fun i => (ell i).val) f
          ((succBlockShape m h).leviEmbedding F b * k) 1‖ ≤
          C * B ^ e *
            ‖(((⟨⟩ : LocalFieldData F).leviHalfModulus (succBlockShape m h) b : ℂˣ) : ℂ)⁻¹‖ *
            ((((⟨⟩ : LocalFieldData F).determinantNorm (m 0 + 1) (b 0) : ℝ≥0) : ℝ) ^ (-u) *
              (((⟨⟩ : LocalFieldData F).determinantNorm (m 1 + 1) (b 1) : ℝ≥0) : ℝ) ^ u) := by
  classical
  choose B hB hgrowth using fun i => exists_functional_growth F ψ (τ i) (hτ i) (ell i)
  refine ⟨∏ i, B i, ?_, fun u f => ?_⟩
  · rw [Fin.prod_univ_two]
    exact one_le_mul_of_one_le_of_one_le (hB 0) (hB 1)
  obtain ⟨C, hC0, hC⟩ := exists_integral_growth F h τ
    (twoBlockOppositeTwistBlocks F m τ u) (fun i => (ell i).val)
    (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F))
    B (fun i => zero_le_one.trans (hB i)) hgrowth f
  refine ⟨C, hC0, fun k hk e b hb => ?_⟩
  have hcov := scalarSection_covariant (fun i => (ell i).val) f
    ((succBlockShape m h).oppositeLeviInParabolic F b)
    ((succBlockShape m h).oppositeLeviProjection_section F b) k 1
  rw [GeneralLinear.BlockShape.oppositeLeviInParabolic_val, one_mul] at hcov
  have hp0 : 0 < (((⟨⟩ : LocalFieldData F).determinantNorm (m 0 + 1) (b 0) : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  have hp1 : 0 < (((⟨⟩ : LocalFieldData F).determinantNorm (m 1 + 1) (b 1) : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  rw [hcov, scalarSection_def,
    tensorContraction_blockTensor_twist F h τ u (fun i => (ell i).val),
    norm_mul, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hp0,
    Complex.norm_cpow_eq_rpow_re_of_pos hp1, Complex.neg_re, Complex.ofReal_re]
  have hnonneg : 0 ≤
      ‖(((⟨⟩ : LocalFieldData F).leviHalfModulus (succBlockShape m h) b : ℂˣ) : ℂ)⁻¹‖ *
        ((((⟨⟩ : LocalFieldData F).determinantNorm (m 0 + 1) (b 0) : ℝ≥0) : ℝ) ^ (-u) *
          (((⟨⟩ : LocalFieldData F).determinantNorm (m 1 + 1) (b 1) : ℝ≥0) : ℝ) ^ u) := by
    positivity
  calc
    _ ≤ ‖(((⟨⟩ : LocalFieldData F).leviHalfModulus (succBlockShape m h) b : ℂˣ) : ℂ)⁻¹‖ *
        ((((⟨⟩ : LocalFieldData F).determinantNorm (m 0 + 1) (b 0) : ℝ≥0) : ℝ) ^ (-u) *
          (((⟨⟩ : LocalFieldData F).determinantNorm (m 1 + 1) (b 1) : ℝ≥0) : ℝ) ^ u) *
        (C * (∏ i, B i) ^ e) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hC k hk e b hb) hnonneg
    _ = _ := by ring

end Sections

end Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
