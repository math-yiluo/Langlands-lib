import Langlands.Representation.Whittaker.TwoBlockInducingCovarianceProof
import Langlands.AllField.Representation.Whittaker.TwoBlockInducingCovarianceStatement
/-! # Proof of scalar Whittaker covariance for actual two-block induction -/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding TwoBlockInducedCarrier TwoBlockInducingWhittakerCovarianceStatement hasCompactSupport_twoBlockCellRestriction twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellRestriction twoBlockCellSubmodule twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockInducingWhittakerCovariance twoBlockParabolic twoBlockRestriction
open Langlands.AllField.Whittaker

open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uV

section Tensor


end Tensor

/-- The actual normalized covariance law and determinant-one of the two
unipotent blocks give the required scalar left covariance. -/
theorem twoBlockInducingWhittakerCovariance :
    TwoBlockInducingWhittakerCovarianceStatement.{uF, uV} := by
  intro F _ _ _ _ ψ a b V₁ _ _ V₂ _ _ π₁ π₂
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.generalLinearTopologicalGroup (a + 1 + (b + 1))
  intro ℓ₁ hℓ₁ ℓ₂ hℓ₂ f u₁ u₂ g
  let m : (twoBlockShape a b).Levi F :=
    (Shahidi.twoBlockLeviEquiv (Nat.succ_pos a) (Nat.succ_pos b) F).symm
      (u₁.val, u₂.val)
  have hnorm (r : ℕ) (u : upperUnipotent r F) :
      T.determinantNorm r u.val = 1 := by
    have hd : GeneralLinear.determinant u.val = 1 :=
      Units.ext (RankinSelberg.unipotent_det u)
    change T.normalizedAbsUnits (GeneralLinear.determinant u.val) = 1
    rw [hd, map_one]
  have hmod : T.leviModulus (twoBlockShape a b) m = 1 := by
    rw [T.leviModulus_twoBlocks]
    change T.determinantNorm (a + 1) u₁.val ^ (b + 1) /
      T.determinantNorm (b + 1) u₂.val ^ (a + 1) = 1
    simp only [hnorm, one_pow, div_one]
  have he : ((twoBlockShape a b).leviInParabolic F m).val =
      blockSum (u₁.val, u₂.val) := by
    exact Shahidi.twoBlocks_leviEmbedding (Nat.succ_pos a) (Nat.succ_pos b) F m
  have hc := T.normalizedProductInduced_covariant (twoBlockShape a b)
    (Shahidi.pairFamily π₁ π₂) f
    ((twoBlockShape a b).leviInParabolic F m) g
  rw [he, BlockShape.leviProjection_section, hmod] at hc
  simp only [Units.val_one, NNReal.sqrt_one, NNReal.coe_one,
    Complex.ofReal_one, one_smul] at hc
  change Shahidi.pairFunctional ℓ₁ ℓ₂
    (Induction.eval (twoBlockParabolic F a b) (twoBlockInducingRepresentation F a b π₁ π₂)
      f (blockSum (u₁.val, u₂.val) * g)) = _
  rw [hc]
  exact pairFunctional_blockTensor_unipotent ψ a b π₁ π₂ ℓ₁ hℓ₁ ℓ₂ hℓ₂ u₁ u₂ _

end Langlands.AllField.Whittaker
