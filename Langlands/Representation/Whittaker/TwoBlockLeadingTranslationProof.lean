import Langlands.Representation.Whittaker.TwoBlockLeadingTranslationStatement
import Langlands.Representation.Whittaker.TwoBlockCellUnipotentStabilityProof
import Langlands.Representation.Shahidi.IntertwiningIntegral

/-! # Leading exchanged block translation of actual cell vectors -/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear

universe uF uV

section Algebra

variable {R : Type uF} [Field R] (m n : ℕ)

/-- The cell point identity for arbitrary exchanged diagonal blocks. -/
theorem blockWeyl_intertwiningUnipotent_mul_exchanged_blockSum
    (h : Langlands.GeneralLinear m R) (g : Langlands.GeneralLinear n R)
    (x : Matrix (Fin n) (Fin m) R) :
    Shahidi.blockWeyl m n R * Shahidi.intertwiningUnipotent m n R x *
        Shahidi.swapRank m n R (blockSum (g, h)) =
      blockSum (h, g) *
        (Shahidi.blockWeyl m n R *
          Shahidi.intertwiningUnipotent m n R (g⁻¹.val * x * h.val)) := by
  rw [Shahidi.intertwiningUnipotent, Shahidi.intertwiningUnipotent,
    mul_assoc, ← map_mul, Shahidi.upper_mul_blockSum, map_mul,
    ← mul_assoc, ← mul_assoc]
  congr 1
  rw [← Shahidi.blockWeyl_conjugate_blockSum m n R g h, inv_mul_cancel_right]

end Algebra

/-- Right translation by the exchanged leading block preserves support in the
cell and compact support of the restriction, with the actual normalized law. -/
theorem twoBlockLeadingTranslation : TwoBlockLeadingTranslationStatement.{uF, uV} := by
  intro p _ F a b V₁ V₂ _ _ _ _ π₁ π₂
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (a + 1 + (b + 1))
  dsimp only
  intro g f
  let s (k : Langlands.GeneralLinear (b + 1) F.Carrier) :=
    Shahidi.swapRank (a + 1) (b + 1) F.Carrier (blockSum (k, 1))
  let m (k : Langlands.GeneralLinear (b + 1) F.Carrier) :=
    (Shahidi.twoBlockLeviEquiv (Nat.succ_pos a) (Nat.succ_pos b) F.Carrier).symm (1, k)
  let q (k : Langlands.GeneralLinear (b + 1) F.Carrier) :=
    (twoBlockShape a b).leviInParabolic F.Carrier (m k)
  have hq (k : Langlands.GeneralLinear (b + 1) F.Carrier) :
      (q k).val = blockSum (1, k) :=
    Shahidi.twoBlocks_leviEmbedding (Nat.succ_pos a) (Nat.succ_pos b) F.Carrier (m k)
  have hpt (k : Langlands.GeneralLinear (b + 1) F.Carrier)
      (x : Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier) :
      twoBlockCellPoint F a b x * s k =
        (q k).val * twoBlockCellPoint F a b (k⁻¹.val * x) := by
    simpa only [twoBlockCellPoint, s, hq, Units.val_one, Matrix.mul_one] using
      blockWeyl_intertwiningUnipotent_mul_exchanged_blockSum (a + 1) (b + 1) 1 k x
  have hcell (k : Langlands.GeneralLinear (b + 1) F.Carrier)
      {z : Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier}
      (hz : z ∈ twoBlockCell F a b) : z * s k ∈ twoBlockCell F a b := by
    obtain ⟨r, x, rfl⟩ := hz
    refine ⟨r * q k, k⁻¹.val * x, ?_⟩
    have h := hpt k x
    rw [twoBlockCellPoint, twoBlockCellPoint] at h
    simp only [Subgroup.coe_mul, mul_assoc] at h ⊢
    rw [h]
  let φ := affineHomeomorph (m := a + 1) F.Carrier g 0 1
  have hφ (x : Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier) :
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

end Langlands.Whittaker
