import Langlands.Representation.Whittaker.TwoBlockCellUnipotentStabilityProof
import Langlands.AllField.Representation.Whittaker.TwoBlockCellUnipotentStabilityStatement
/-!
# Proof of the upper unipotent stability of the two-block cell submodule

Read through the rank exchange `GL_(A+B) ≅ GL_(B+A)`, an upper unipotent `u`
lies in the standard parabolic of shape `(B, A)`, with diagonal blocks `α`, `δ`
and upper-right block `β`. Then `w n(x) u = diag(δ, α) w n(y)` with
`y = α⁻¹ (β + x δ)`. So right translation by `u` preserves the cell, and the
restriction of `ξ(u) f` is `ρ(diag(δ, α))` applied to the restriction of `f`
composed with the affine homeomorphism `x ↦ α⁻¹ (β + x δ)`.
-/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker

open Langlands.GeneralLinear

universe uF uV u

section Matrix


end Matrix

section Cell

variable (F : Type uF) [Field F] (a b : ℕ)

/-- The element `u` read in the parabolic of the exchanged shape `(B, A)`. -/
def exchangedParabolic (u : upperUnipotent (a + 1 + (b + 1)) F) :
    (Shahidi.twoBlocks (b + 1) (a + 1) (Nat.succ_pos b) (Nat.succ_pos a)).parabolic F :=
  ⟨(Shahidi.swapRank (a + 1) (b + 1) F).symm u.val,
    swapRank_symm_mem_parabolic (Nat.succ_pos a) (Nat.succ_pos b) F u⟩

theorem swapRank_exchangedParabolic (u : upperUnipotent (a + 1 + (b + 1)) F) :
    Shahidi.swapRank (a + 1) (b + 1) F (exchangedParabolic F a b u).val = u.val :=
  (Shahidi.swapRank (a + 1) (b + 1) F).apply_symm_apply u.val

/-- The Levi element `diag(δ, α)` of `P` attached to `u`. -/
def unipotentLeviFactor (u : upperUnipotent (a + 1 + (b + 1)) F) :
    twoBlockParabolic F a b :=
  ⟨blockSum ((parabolicDiagonal (Nat.succ_pos a) (Nat.succ_pos b) F
      (exchangedParabolic F a b u)).2,
    (parabolicDiagonal (Nat.succ_pos a) (Nat.succ_pos b) F
      (exchangedParabolic F a b u)).1),
    blockSum_mem_twoBlocks_parabolic (Nat.succ_pos a) (Nat.succ_pos b) F _ _⟩

/-- The coordinate change `x ↦ α⁻¹ (β + x δ)` attached to `u`. -/
def unipotentShift (u : upperUnipotent (a + 1 + (b + 1)) F)
    (x : Matrix (Fin (b + 1)) (Fin (a + 1)) F) :
    Matrix (Fin (b + 1)) (Fin (a + 1)) F :=
  parabolicShift (Nat.succ_pos a) (Nat.succ_pos b) F (exchangedParabolic F a b u) x

/-- `w n(x) u = diag(δ, α) w n(y)`, with `y` the shifted coordinate. -/
theorem twoBlockCellPoint_mul_upperUnipotent (u : upperUnipotent (a + 1 + (b + 1)) F)
    (x : Matrix (Fin (b + 1)) (Fin (a + 1)) F) :
    twoBlockCellPoint F a b x * u.val =
      (unipotentLeviFactor F a b u : Langlands.GeneralLinear (a + 1 + (b + 1)) F) *
        twoBlockCellPoint F a b (unipotentShift F a b u x) := by
  rw [twoBlockCellPoint, twoBlockCellPoint, ← swapRank_exchangedParabolic F a b u]
  exact blockWeyl_mul_intertwiningUnipotent_mul_swapRank (Nat.succ_pos a) (Nat.succ_pos b)
    F x (exchangedParabolic F a b u)

/-- Right translation by an upper unipotent matrix preserves the cell. -/
theorem mul_upperUnipotent_mem_twoBlockCell
    {g : Langlands.GeneralLinear (a + 1 + (b + 1)) F} (hg : g ∈ twoBlockCell F a b)
    (u : upperUnipotent (a + 1 + (b + 1)) F) :
    g * u.val ∈ twoBlockCell F a b := by
  obtain ⟨q, x, rfl⟩ := hg
  refine ⟨q * unipotentLeviFactor F a b u, unipotentShift F a b u x, ?_⟩
  have h := twoBlockCellPoint_mul_upperUnipotent F a b u x
  rw [twoBlockCellPoint, twoBlockCellPoint] at h
  simp only [Subgroup.coe_mul, mul_assoc] at h ⊢
  rw [h]

end Cell

/-- JPSS (9.1), upper unipotent stability: right translation by every upper
unipotent matrix maps the cell submodule `D` into itself. -/
theorem twoBlockCellUnipotentStability : TwoBlockCellUnipotentStabilityStatement.{uF, uV} := by
  intro F _ _ _ _ a b V₁ V₂ _ _ _ _ π₁ π₂ u f hf
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨hsupp, hcpt⟩ := hf
  refine ⟨fun g hg => ?_, ?_⟩
  · have h1 : g * u.val ∈ twoBlockCell F a b := hsupp hg
    have h2 := mul_upperUnipotent_mem_twoBlockCell F a b h1 u⁻¹
    rwa [Subgroup.coe_inv, mul_inv_cancel_right] at h2
  · let g' := exchangedParabolic F a b u
    let φ := affineHomeomorph F
      (parabolicDiagonal (Nat.succ_pos a) (Nat.succ_pos b) F g').1
      (parabolicCorner F g'.val)
      (parabolicDiagonal (Nat.succ_pos a) (Nat.succ_pos b) F g').2
    have hR : twoBlockRestriction F a b π₁ π₂ (twoBlockInduced F a b π₁ π₂ u.val f) =
        (twoBlockInducingRepresentation F a b π₁ π₂ (unipotentLeviFactor F a b u)) ∘
          (twoBlockRestriction F a b π₁ π₂ f) ∘ φ := by
      funext x
      change twoBlockEval F a b π₁ π₂ f (twoBlockCellPoint F a b x * u.val) =
        twoBlockInducingRepresentation F a b π₁ π₂ (unipotentLeviFactor F a b u)
          (twoBlockEval F a b π₁ π₂ f (twoBlockCellPoint F a b (unipotentShift F a b u x)))
      rw [twoBlockCellPoint_mul_upperUnipotent]
      exact f.1.2 (unipotentLeviFactor F a b u) _
    rw [hR]
    exact (hcpt.comp_homeomorph φ).comp_left (map_zero _)

end Langlands.AllField.Whittaker
