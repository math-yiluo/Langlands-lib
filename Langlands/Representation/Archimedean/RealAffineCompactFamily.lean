import Langlands.Representation.Archimedean.RealCompactExponentFamily

/-! # Simultaneous exponent shifts and compact transport of real block maps -/

noncomputable section

open Langlands.LocalFactor.Archimedean
open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealExponentDeformation

open GramFormula RealBlockFrobeniusMap RealBlockMultiplier

/-- Move each block along its assigned exponent line. -/
def shiftedBlocks (bs : List (RealBlock × ℂ)) (z : ℂ) : List RealBlock :=
  bs.map fun (b, t) => shiftBlock (z * t) b

/-- The slope at a diagonal position is the slope of its block. -/
def positionSlope : List (RealBlock × ℂ) → ℕ → ℂ
  | [], _ => 0
  | (.character _, t) :: _, 0 => t
  | (.character _, _) :: bs, j + 1 => positionSlope bs j
  | (.induced _, t) :: _, 0 => t
  | (.induced _, t) :: _, 1 => t
  | (.induced _, _) :: bs, j + 2 => positionSlope bs j

@[simp]
theorem realRank_shiftedBlocks (bs : List (RealBlock × ℂ)) (z : ℂ) :
    realRank (shiftedBlocks bs z) = realRank (bs.map Prod.fst) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      rcases b with ⟨b, t⟩
      simpa only [shiftedBlocks, List.map_cons, realRank_cons, shiftBlock_rank] using
        congrArg (b.rank + ·) ih

theorem positionExponent_shiftedBlocks (bs : List (RealBlock × ℂ)) (z : ℂ) (j : ℕ) :
    realPositionExponent (shiftedBlocks bs z) j =
      realPositionExponent (bs.map Prod.fst) j + z * positionSlope bs j := by
  induction bs generalizing j with
  | nil => simp [shiftedBlocks, realPositionExponent, positionSlope]
  | cons b bs ih =>
      rcases b with ⟨b, t⟩
      cases b with
      | character d =>
          cases j with
          | zero => rfl
          | succ j => exact ih j
      | induced d =>
          rcases j with _ | _ | j
          · change d.exponent + z * t + (d.weight.natAbs : ℂ) / 2 =
              d.exponent + (d.weight.natAbs : ℂ) / 2 + z * t
            ring
          · change d.exponent + z * t - (d.weight.natAbs : ℂ) / 2 =
              d.exponent - (d.weight.natAbs : ℂ) / 2 + z * t
            ring
          · exact ih j

theorem isExponentShift_shiftedBlocks {n : ℕ} (bs : List (RealBlock × ℂ))
    (hr : realRank (bs.map Prod.fst) = n) (z : ℂ) :
    IsExponentShift n (bs.map Prod.fst) (shiftedBlocks bs z) (fun i => positionSlope bs i) z := by
  refine IsExponentShift.of_forall₂ hr ?_ (fun i => positionExponent_shiftedBlocks bs z i)
  clear hr
  induction bs with
  | nil => exact .nil
  | cons b bs ih =>
      rcases b with ⟨b, t⟩
      refine .cons ?_ ih
      cases b <;> rfl

variable {n p : ℕ} {ds es ds' es' : List RealBlock} {ε ε' : ℤ} {σ σ' : ℂ}
variable {μ : ℤ → ℂ} {a b : Fin n → ℂ} {z : ℂ}

/-- Compact transfer commutes with a block map of the same mode symbol. -/
theorem compactEquiv_blockFrobMap
    (ha : IsExponentShift n ds ds' a z) (hb : IsExponentShift n es es' b z)
    (h : IsBlockFrobData n ds es p ε σ μ) (hz : IsBlockFrobData n ds' es' p ε' σ' μ)
    (f : KF n ds) :
    hb.compactEquiv (blockFrobMap h f) = blockFrobMap hz (ha.compactEquiv f) := by
  apply ext_of_eqOn
  exact (compactEquiv_eqOn hb.rank hb.rank' hb.forward hb.backward (blockFrobMap h f)).trans
    (blockFrobMap_eqOn h hz
      (compactEquiv_eqOn ha.rank ha.rank' ha.forward ha.backward f)).symm

/-- The affine Lie intertwining identity on fixed compact models follows from the
recurrence for the block map on the shifted standard modules. -/
def RealAffineCompactFamilyStatement : Prop :=
  ∀ {ds₁ es₁ : List RealBlock},
    IsExponentShift n ds ds' a z →
    IsExponentShift n es es' b z →
    ∀ (h₁ : IsExponentShift n ds ds₁ a 1) (h₂ : IsExponentShift n es es₁ b 1)
      (h : IsBlockFrobData n ds es p ε σ μ),
    IsBlockFrobData n ds' es' p ε' σ' μ →
    IsRecurrent (realPositionExponent ds' p - realPositionExponent ds' (p + 1) + 1) ε' μ →
    ∀ (X : Matrix (Fin n) (Fin n) ℝ) (f : KF n ds),
      blockFrobMap h (realStandardLie n ds (1 ⊗ₜ X) f + z • lieIncrement h₁ X f) =
        realStandardLie n es (1 ⊗ₜ X) (blockFrobMap h f) +
          z • lieIncrement h₂ X (blockFrobMap h f)

theorem realAffineCompactFamily :
    RealAffineCompactFamilyStatement (n := n) (ds := ds) (es := es) (ds' := ds') (es' := es')
      (p := p) (ε := ε) (ε' := ε') (σ := σ) (σ' := σ') (μ := μ) (a := a) (b := b) (z := z) := by
  intro ds₁ es₁ ha hb h₁ h₂ h hz hrec X f
  have hLie : blockFrobMap h (ha.transportedLie X f) =
      hb.transportedLie X (blockFrobMap h f) := by
    apply hb.compactEquiv.injective
    rw [compactEquiv_blockFrobMap ha hb h hz]
    simp only [IsExponentShift.transportedLie, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    rw [compactEquiv_blockFrobMap ha hb h hz, blockFrobMap_rightDerivative hz hrec]
  rw [transportedLie_eq_affine ha h₁, transportedLie_eq_affine hb h₂] at hLie
  exact hLie

end Langlands.Archimedean.RealExponentDeformation
