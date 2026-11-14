import Langlands.Representation.Whittaker.TwoBlockCellCoefficientProof
import Langlands.AllField.Representation.Whittaker.TwoBlockCellCoefficientStatement
import Langlands.AllField.Representation.Whittaker.TwoBlockCellSectionProof
import Langlands.AllField.Representation.Whittaker.TwoBlockJacquetFunctionalExtensionProof
import Langlands.AllField.Representation.Whittaker.TwoBlockLeadingTranslationProof
/-! # Pure-tensor cell sections yield actual scalar Whittaker coefficients -/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding TwoBlockCellCoefficientStatement TwoBlockCellJacquetIntegrabilityStatement TwoBlockCellSectionStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier TwoBlockInducingWhittakerCovarianceStatement TwoBlockJacquetCovarianceStatement TwoBlockJacquetFunctionalExtensionStatement TwoBlockLeadingTranslationStatement exchangedParabolic exists_openSubgroup_subset_parabolic_mul_opposite hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell oppositeLower swapRank_exchangedParabolic twoBlockCell twoBlockCellCoefficient twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellJacquetIntegrability twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSection twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockInducingWhittakerCovariance twoBlockJacquetCovariance twoBlockJacquetFunctionalExtension twoBlockLeadingTranslation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uV

/-- Evaluate the extended cell functional on a pure-tensor section and its
leading-block translates. -/
theorem twoBlockCellCoefficient : TwoBlockCellCoefficientStatement.{uF, uV} := by
  intro F _ _ _ _ a b V₁ V₂ _ _ _ _ π₁ π₂ hπ₁ hπ₂
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.fieldT2
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  dsimp only
  intro ψ ℓ₁ hℓ₁ ℓ₂ hℓ₂ μ _ Ψ v₁ v₂
  obtain ⟨f, hf, hres⟩ := twoBlockCellSection F a b π₁ π₂ hπ₁ hπ₂
    Ψ (Shahidi.pairTensor v₁ v₂)
  obtain ⟨L, hL⟩ := twoBlockJacquetFunctionalExtension F a b π₁ π₂
    ψ ℓ₁ hℓ₁ ℓ₂ hℓ₂ μ
  refine ⟨coefficientMap (twoBlockInduced F a b π₁ π₂) L f, ⟨L, ⟨f, rfl⟩⟩, ?_⟩
  intro g
  let s := Shahidi.swapRank (a + 1) (b + 1) F
    (GeneralLinear.blockSum (g, 1))
  let m := (Shahidi.twoBlockLeviEquiv
    (Nat.succ_pos a) (Nat.succ_pos b) F).symm (1, g)
  obtain ⟨htrans, hval⟩ := twoBlockLeadingTranslation F a b π₁ π₂ g ⟨f, hf⟩
  change L.val (twoBlockInduced F a b π₁ π₂ s f) = _
  rw [hL ⟨_, htrans⟩]
  have hint (x : Matrix (Fin (b + 1)) (Fin (a + 1)) F) :
      Shahidi.jacquetIntegrand a b ψ (Shahidi.pairFunctional ℓ₁ ℓ₂)
          (twoBlockEval F a b π₁ π₂ (twoBlockInduced F a b π₁ π₂ s f)) x =
        (((T.leviHalfModulus (twoBlockShape a b) m : ℂˣ) : ℂ) *
          (ℓ₁ v₁ * ℓ₂ (π₂ g v₂))) *
          (ψ.complex (-(x (Fin.last b) 0)) * Ψ (g⁻¹.val * x)) := by
    change Shahidi.intertwiningJacquetKernel a b ψ x *
      Shahidi.pairFunctional ℓ₁ ℓ₂
        (twoBlockRestriction F a b π₁ π₂ (twoBlockInduced F a b π₁ π₂ s f) x) = _
    rw [hval]
    change Shahidi.intertwiningJacquetKernel a b ψ x *
      Shahidi.pairFunctional ℓ₁ ℓ₂
        (((T.leviHalfModulus (twoBlockShape a b) m : ℂˣ) : ℂ) •
          (twoBlockShape a b).blockTensor (Shahidi.pairFamily π₁ π₂) m
            (twoBlockRestriction F a b π₁ π₂ f (g⁻¹.val * x))) = _
    rw [hres, map_smul, map_smul, Shahidi.blockTensor_pairTensor, map_smul,
      Shahidi.pairFunctional_pairTensor]
    simp only [m, Shahidi.twoBlockLeviEquiv_symm_first,
      Shahidi.twoBlockLeviEquiv_symm_second, map_one, Module.End.one_apply,
      smul_eq_mul, Shahidi.intertwiningJacquetKernel_eq_neg_corner]
    ring
  exact (integral_congr_ae (Filter.Eventually.of_forall hint)).trans (integral_const_mul _ _)

end Langlands.AllField.Whittaker
