import Langlands.GroupScheme.RelativeUnipotent.RootWeightFiltration
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Positive integral scaling of actual root-weight filtrations -/

noncomputable section

set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupTheory.HeightFiltration

variable {K : Type*} [Group K] {n : ℕ}

/-- Scaling all generator weights and the cutoff by the same positive natural
number leaves the actual generated subgroup unchanged. -/
theorem level_mul_weights (H : Fin n → Subgroup K) (w : Fin n → ℕ)
    (q : ℕ) (hq : 0 < q) (d : ℕ) :
    level H (fun k => q * w k) (q * d) = level H w d := by
  have hc (a b : ℕ) : q * a ≤ q * b ↔ a ≤ b :=
    ⟨fun h => by nlinarith, Nat.mul_le_mul_left q⟩
  simp only [level, factor, hc]

end Langlands.GroupTheory.HeightFiltration

namespace Langlands.GroupScheme.RelativeUnipotent.RootWeightData

open LocalSplitCell Langlands.GroupTheory

variable {R : Type u} [CommRing R]
  {U : GroupScheme (Spec (CommRingCat.of R))} {C : RootHeightChart U}
  (W : RootWeightData C)

/-- A positive integral multiple of the secondary weights on the same actual
ordered root chart, with its commutator bound proved by cancelling the scale. -/
def scale (q : ℕ) (hq : 0 < q) : RootWeightData C where
  weight k := q * W.weight k
  commutator T k l := by
    rw [← Nat.mul_add, HeightFiltration.level_mul_weights _ _ q hq]
    exact W.commutator T k l

@[simp] theorem scale_weight (q : ℕ) (hq : 0 < q) (k : Fin C.dimension) :
    (W.scale q hq).weight k = q * W.weight k := rfl

/-- Positive scaling leaves the actual positive subgroup functor unchanged. -/
theorem scale_subgroup_zero (q : ℕ) (hq : 0 < q) :
    (W.scale q hq).subgroup 0 = W.subgroup 0 := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [mem_subgroup_iff, W.mem_subgroup_iff]
  simp only [scale_weight, Nat.zero_add, Nat.lt_one_iff, Nat.mul_eq_zero,
    hq.ne', false_or]

/-- The scale multiplies the positive cutoff; this exact index formula includes
empty weight families and zero weights. -/
theorem scale_subgroup (q : ℕ) (hq : 0 < q) (d : ℕ) :
    (W.scale q hq).subgroup (q * (d + 1) - 1) = W.subgroup d := by
  have he : q * (d + 1) - 1 + 1 = q * (d + 1) :=
    Nat.sub_add_cancel (Nat.mul_pos hq (Nat.zero_lt_succ d))
  apply SubgroupFunctor.ext
  intro T
  change HeightFiltration.level (rootFactor C.roots ULift.up T)
    (fun k => q * W.weight k) (q * (d + 1) - 1 + 1) =
      HeightFiltration.level (rootFactor C.roots ULift.up T) W.weight (d + 1)
  rw [he, HeightFiltration.level_mul_weights _ _ q hq]

/-- The actual term comparison under the exact scaled-cutoff reindexing. -/
def scaleTermIso (q : ℕ) (hq : 0 < q) (d : ℕ) :
    (W.scale q hq).groupScheme (q * (d + 1) - 1) ≅ W.groupScheme d := by
  let h : (W.subgroup d).IsRepresentedBy
      ((W.scale q hq).inclusion (q * (d + 1) - 1)) :=
    ⟨((W.scale q hq).isRepresentedBy_inclusion _).1,
      ((W.scale q hq).isRepresentedBy_inclusion _).2.trans (W.scale_subgroup q hq d)⟩
  exact h.isoOfIsRepresentedBy (W.isRepresentedBy_inclusion d)

/-- The comparison retains the original actual inclusion into the chart group. -/
theorem scaleTermIso_hom_comp (q : ℕ) (hq : 0 < q) (d : ℕ) :
    (W.scaleTermIso q hq d).hom ≫ W.inclusion d =
      (W.scale q hq).inclusion (q * (d + 1) - 1) :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end Langlands.GroupScheme.RelativeUnipotent.RootWeightData
