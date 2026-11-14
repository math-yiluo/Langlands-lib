import Langlands.Representation.Whittaker.TwoBlockLeadingTranslationProof
import Langlands.AllField.Representation.Whittaker.TwoBlockCellUnipotentStabilityProof
import Langlands.AllField.Representation.Whittaker.TwoBlockLeadingTranslationStatement
/-! # Leading exchanged block translation of actual cell vectors -/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier TwoBlockLeadingTranslationStatement exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockLeadingTranslation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker

open Langlands.GeneralLinear

universe uF uV

section Algebra


end Algebra

/-- Right translation by the exchanged leading block preserves support in the
cell and compact support of the restriction, with the actual normalized law. -/
theorem twoBlockLeadingTranslation : TwoBlockLeadingTranslationStatement.{uF, uV} := by
  intro F _ _ _ _ a b V₁ V₂ _ _ _ _ π₁ π₂
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (a + 1 + (b + 1))
  dsimp only
  intro g f
  let s (k : Langlands.GeneralLinear (b + 1) F) :=
    Shahidi.swapRank (a + 1) (b + 1) F (blockSum (k, 1))
  let m (k : Langlands.GeneralLinear (b + 1) F) :=
    (Shahidi.twoBlockLeviEquiv (Nat.succ_pos a) (Nat.succ_pos b) F).symm (1, k)
  let q (k : Langlands.GeneralLinear (b + 1) F) :=
    (twoBlockShape a b).leviInParabolic F (m k)
  have hq (k : Langlands.GeneralLinear (b + 1) F) :
      (q k).val = blockSum (1, k) :=
    Shahidi.twoBlocks_leviEmbedding (Nat.succ_pos a) (Nat.succ_pos b) F (m k)
  have hpt (k : Langlands.GeneralLinear (b + 1) F)
      (x : Matrix (Fin (b + 1)) (Fin (a + 1)) F) :
      twoBlockCellPoint F a b x * s k =
        (q k).val * twoBlockCellPoint F a b (k⁻¹.val * x) := by
    simpa only [twoBlockCellPoint, s, hq, Units.val_one, Matrix.mul_one] using
      blockWeyl_intertwiningUnipotent_mul_exchanged_blockSum (a + 1) (b + 1) 1 k x
  have hcell (k : Langlands.GeneralLinear (b + 1) F)
      {z : Langlands.GeneralLinear (a + 1 + (b + 1)) F}
      (hz : z ∈ twoBlockCell F a b) : z * s k ∈ twoBlockCell F a b := by
    obtain ⟨r, x, rfl⟩ := hz
    refine ⟨r * q k, k⁻¹.val * x, ?_⟩
    have h := hpt k x
    rw [twoBlockCellPoint, twoBlockCellPoint] at h
    simp only [Subgroup.coe_mul, mul_assoc] at h ⊢
    rw [h]
  let φ := affineHomeomorph (m := a + 1) F g 0 1
  have hφ (x : Matrix (Fin (b + 1)) (Fin (a + 1)) F) :
      φ x = g⁻¹.val * x := by
    simp only [φ, affineHomeomorph_apply, Units.val_one, Matrix.mul_one, zero_add]
  have hR : twoBlockRestriction F a b π₁ π₂
      (twoBlockInduced F a b π₁ π₂ (s g) f.val) =
        (twoBlockInducingRepresentation F a b π₁ π₂ (q g)) ∘
          (twoBlockCellRestriction F a b π₁ π₂ f) ∘ φ := by
    funext x
    change twoBlockEval F a b π₁ π₂ f.val (twoBlockCellPoint F a b x * s g) =
      twoBlockInducingRepresentation F a b π₁ π₂ (q g)
        (twoBlockEval F a b π₁ π₂ f.val (twoBlockCellPoint F a b (φ x)))
    rw [hφ, hpt]
    exact f.val.1.2 (q g) _
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z hz
    have h₁ : z * s g ∈ twoBlockCell F a b := f.property.1 hz
    have h₂ := hcell g⁻¹ h₁
    have hinv : s g⁻¹ = (s g)⁻¹ := by
      simp only [s, ← map_inv, Prod.inv_mk, inv_one]
    simpa only [hinv, mul_inv_cancel_right] using h₂
  · rw [hR]
    exact ((hasCompactSupport_twoBlockCellRestriction F a b π₁ π₂ f).comp_homeomorph φ).comp_left
      (map_zero _)
  · intro x
    have hc := T.normalizedProductInduced_covariant (twoBlockShape a b)
      (Shahidi.pairFamily π₁ π₂) f.val (q g)
        (twoBlockCellPoint F a b (g⁻¹.val * x))
    rw [BlockShape.leviProjection_section] at hc
    change twoBlockEval F a b π₁ π₂ f.val (twoBlockCellPoint F a b x * s g) = _
    rw [hpt]
    rw [T.leviHalfModulus_apply]
    exact hc

end Langlands.AllField.Whittaker
