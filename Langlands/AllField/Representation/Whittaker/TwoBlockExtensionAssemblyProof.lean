import Langlands.Representation.Whittaker.TwoBlockExtensionAssemblyProof
import Langlands.AllField.HarmonicAnalysis.MatrixFourierSliceProof
import Langlands.AllField.Representation.Induction.BlockEquivalence
import Langlands.AllField.Representation.Whittaker.TwoBlockCellCoefficientProof
import Langlands.AllField.Representation.Whittaker.TwoBlockExtensionAssemblyStatement
/-! # Conditional proof of the JPSS two-block extension -/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding TwoBlockCellCoefficientStatement TwoBlockCellJacquetIntegrabilityStatement TwoBlockCellSectionStatement TwoBlockCellUnipotentStabilityStatement TwoBlockExtensionAssemblyStatement TwoBlockInducedCarrier TwoBlockInducingWhittakerCovarianceStatement TwoBlockJacquetCovarianceStatement TwoBlockJacquetFunctionalExtensionStatement TwoBlockLeadingTranslationStatement TwoBlockWhittakerExtensionStatement exchangedParabolic exists_openSubgroup_subset_parabolic_mul_opposite hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell oppositeLower swapRank_exchangedParabolic twoBlockCell twoBlockCellCoefficient twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellJacquetIntegrability twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSection twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockHalfModulus_mul_detPow twoBlockInduced twoBlockInducingRepresentation twoBlockInducingWhittakerCovariance twoBlockJacquetCovariance twoBlockJacquetFunctionalExtension twoBlockLeadingTranslation twoBlockParabolic twoBlockRestriction twoBlockWhittakerExtension_of_rowFourierSurjectivity unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement functionalsCongr isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

universe uF uV₁ uV₂

private theorem sqrt_inv_pow_mul (d : ℝ) (hd : 0 < d) (A : ℕ) :
    Real.sqrt ((d ^ A)⁻¹) * d ^ A = Real.rpow d ((A : ℝ) / 2) := by
  rw [Real.sqrt_inv, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul hd.le, ← Real.rpow_neg hd.le, ← Real.rpow_add hd]
  congr 1
  ring

/-- The positive induction half and the rectangular Jacobian give the positive
half power in the JPSS leading-block formula. -/
theorem twoBlockHalfModulus_mul_detPow
    (F : Type uF) [Field F] (T : LocalFieldData F)
    (a b : ℕ) (g : GeneralLinear (b + 1) F) :
    ((T.leviHalfModulus (twoBlockShape a b)
      ((Shahidi.twoBlockLeviEquiv (Nat.succ_pos a) (Nat.succ_pos b) F).symm
        (1, g)) : ℂ) * (T.normalizedAbs (Matrix.det g.val) : ℂ) ^ (a + 1)) =
      (Real.rpow (T.normalizedAbs (Matrix.det g.val)) (((a + 1 : ℕ) : ℝ) / 2) : ℂ) := by
  have hmod : T.leviModulus (twoBlockShape a b)
      ((Shahidi.twoBlockLeviEquiv (Nat.succ_pos a) (Nat.succ_pos b) F).symm
        (1, g)) = (T.determinantNorm (b + 1) g ^ (a + 1))⁻¹ := by
    rw [T.leviModulus_twoBlocks]
    simp only [Shahidi.twoBlockLeviEquiv_symm_first,
      Shahidi.twoBlockLeviEquiv_symm_second, map_one, one_pow, one_div]
  rw [T.leviHalfModulus_apply, hmod]
  simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    Real.coe_sqrt, NNReal.coe_inv, NNReal.coe_pow, T.determinantNorm_coe]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
  exact congrArg Complex.ofReal
    (sqrt_inv_pow_mul _ (T.normalizedAbs_pos (GeneralLinear.determinant g).ne_zero) (a + 1))

/-- A one-dimensional standard functional space supplies a functional and
vector with value one. -/
private theorem exists_functional_vector_one
    {K : Type*} [Field K] [TopologicalSpace K]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter K) (n : ℕ)
    (π : Representation ℂ (GeneralLinear (n + 1) K) V)
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π) :
    ∃ (ℓ : glFunctionals ψ n π) (v : V), ℓ.val v = 1 := by
  obtain ⟨e⟩ := hπ.2.2
  let ℓ : glFunctionals ψ n π := e.symm 1
  have hℓ : ℓ ≠ 0 := by
    intro h
    have := congrArg e h
    exact one_ne_zero (by
      simpa only [ℓ, LinearEquiv.apply_symm_apply, map_zero] using this)
  have hval : ℓ.val ≠ 0 := fun h => hℓ (Subtype.ext h)
  obtain ⟨v, hv⟩ := (LinearMap.surjective_iff_ne_zero.mpr hval) 1
  exact ⟨ℓ, v, hv⟩

/-- The full unchanged extension target follows once row Fourier surjectivity
is available for the canonical topology in every dimension. -/
theorem twoBlockWhittakerExtension_of_rowFourierSurjectivity :
    TwoBlockExtensionAssemblyStatement.{uF, uV₁, uV₂} := by
  intro hsurj F _ _ _ _ ψ a b V₁ _ _ V₂ _ _ π₁ π₂ hπ₁ hπ₂
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.fieldT2
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  dsimp only
  let π₁' : Representation ℂ (GeneralLinear (a + 1) F) (ULift.{uV₂} V₁) :=
    (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₁
  let π₂' : Representation ℂ (GeneralLinear (b + 1) F) (ULift.{uV₁} V₂) :=
    (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₂
  have hπ₁' : IsSmooth π₁' := (isSmooth_literalULift_iff π₁).mpr hπ₁.1.1
  have hπ₂' : IsSmooth π₂' := (isSmooth_literalULift_iff π₂).mpr hπ₂.1.1
  intro W₂ hW₂ Φ
  obtain ⟨ℓ₁, v₁, hℓ₁⟩ := exists_functional_vector_one ψ a π₁ hπ₁
  obtain ⟨ℓ₂, v₂, hv₂⟩ := hW₂
  let e₁ : π₁.Equiv π₁' := literalULiftEquiv π₁
  let e₂ : π₂.Equiv π₂' := literalULiftEquiv π₂
  let ℓ₁' : glFunctionals ψ a π₁' := Whittaker.functionalsCongr e₁ ℓ₁
  let ℓ₂' : glFunctionals ψ b π₂' := Whittaker.functionalsCongr e₂ ℓ₂
  let ν : AdditiveHaarMeasure F :=
    normalizedAdditiveHaar F (Classical.choice inferInstance)
  obtain ⟨Ψ, hΨ⟩ := padicMatrixFourierSlice F T a b (hsurj F (b + 1)) ψ ν Φ
  obtain ⟨W, hW, hvalues⟩ := twoBlockCellCoefficient F a b π₁' π₂' hπ₁' hπ₂'
    ψ ℓ₁'.val ℓ₁'.property ℓ₂'.val ℓ₂'.property
    (rectangularMeasure ν (b + 1) (a + 1)) Ψ (ULift.up v₁) (ULift.up v₂)
  refine ⟨W, hW, ?_⟩
  intro g
  rw [twoBlockLeadingEmbedding_eq, hvalues g, hΨ g]
  have hfirst : ℓ₁'.val (ULift.up v₁) = 1 := hℓ₁
  have hsecond : ℓ₂'.val (π₂' g (ULift.up v₂)) = W₂.val g := by
    change ℓ₂.val (π₂ g v₂) = W₂.val g
    exact congrArg (fun H : WhittakerFunctions ψ b => H.val g) hv₂
  rw [hfirst, one_mul, hsecond]
  let m := (Shahidi.twoBlockLeviEquiv
    (Nat.succ_pos a) (Nat.succ_pos b) F).symm (1, g)
  calc
    ((T.leviHalfModulus (twoBlockShape a b) m : ℂ) * W₂.val g) *
        ((T.normalizedAbs (Matrix.det g.val) : ℂ) ^ (a + 1) * Φ (lastRow g)) =
        W₂.val g * Φ (lastRow g) *
          ((T.leviHalfModulus (twoBlockShape a b) m : ℂ) *
            (T.normalizedAbs (Matrix.det g.val) : ℂ) ^ (a + 1)) := by ring
    _ = _ := by rw [twoBlockHalfModulus_mul_detPow]

end Langlands.AllField.Whittaker
