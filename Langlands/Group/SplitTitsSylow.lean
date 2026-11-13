import Langlands.Group.TitsParabolicRigidity
import Mathlib.GroupTheory.Nilpotent

/-! # Sylow subgroups from a split Tits-system Borel -/

noncomputable section

namespace Langlands.Group

open TitsSystem

variable {G W : Type*} [Group G] [Group W]
    {B N U : Subgroup G} {π : N →* W} {S : Set W}

namespace IsTitsSystem

variable (h : IsTitsSystem B N π S)
    (hUB : U ≤ B) (hBU : B ≤ Subgroup.normalizer (U : Set G))
    (hsplit : ∀ b ∈ B, ∃ u ∈ U, ∃ t : N, π t = 1 ∧ b = u * t)

include h hUB hBU hsplit in
/-- If `B = U (B ∩ N)` and `B` normalizes `U`, the normalizer of `U`
in the full Tits-system group is exactly `B`. -/
theorem normalizer_eq_of_split : Subgroup.normalizer (U : Set G) = B := by
  apply le_antisymm _ hBU
  intro g hg
  obtain ⟨w, n, hn, a, ha, b, hb, rfl⟩ := h.exists_mem_cell g
  have hnU : (n : G) ∈ Subgroup.normalizer (U : Set G) := by
    have haU : a ∈ Subgroup.normalizer (U : Set G) := hBU ha
    have hbU : b ∈ Subgroup.normalizer (U : Set G) := hBU hb
    have hgU : a * (n : G) * b ∈ Subgroup.normalizer (U : Set G) := hg
    have hc : a⁻¹ * (a * (n : G) * b) * b⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
      (Subgroup.normalizer (U : Set G)).mul_mem
        ((Subgroup.normalizer (U : Set G)).mul_mem
          ((Subgroup.normalizer (U : Set G)).inv_mem haU) hgU)
        ((Subgroup.normalizer (U : Set G)).inv_mem hbU)
    simpa [mul_assoc] using hc
  have hnB : (n : G) ∈ B := by
    apply h.rep_mem_of_conjugate_le le_rfl n
    intro c hc
    obtain ⟨u, hu, t, ht, rfl⟩ := hsplit c hc
    have hu' : (n : G)⁻¹ * u * n ∈ U :=
      (Subgroup.mem_normalizer_iff''.mp hnU u).mp hu
    have ht' : ((n⁻¹ * t * n : N) : G) ∈ B := by
      apply (h.mem_iff _).mpr
      simp only [map_mul, map_inv, ht, mul_one, inv_mul_cancel]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left] using
      B.mul_mem (hUB hu') ht'
  exact B.mul_mem (B.mul_mem ha hnB) hb

include h hUB hBU hsplit in
/-- A p-subgroup in such a split Borel is maximal when every p-subgroup
of the Borel lies in it. Finiteness is used for the p-group normalizer condition. -/
theorem maximalPSubgroup_of_split [Finite G] {p : ℕ} [Fact p.Prime]
    (hBmax : ∀ P : Subgroup G, P ≤ B → IsPGroup p P → P ≤ U)
    (P : Subgroup G) (hUP : U ≤ P) (hP : IsPGroup p P) : P = U := by
  have hnorm := h.normalizer_eq_of_split hUB hBU hsplit
  have hPU : P ⊓ Subgroup.normalizer (U : Set G) ≤ U := by
    apply hBmax
    · rw [hnorm]
      exact inf_le_right
    · exact hP.to_inf_left
  have hself : Subgroup.normalizer (U.subgroupOf P) = U.subgroupOf P := by
    apply le_antisymm _ Subgroup.le_normalizer
    rw [← Subgroup.subgroupOf_normalizer_eq hUP]
    intro x hx
    exact hPU ⟨x.property, hx⟩
  let : _root_.Group.IsNilpotent P := hP.isNilpotent
  have htop : U.subgroupOf P = ⊤ :=
    normalizerCondition_iff_only_full_group_self_normalizing.mp
      (_root_.Group.normalizerCondition_of_isNilpotent (G := P)) _ hself
  exact le_antisymm ((Subgroup.subgroupOf_eq_top).mp htop) hUP

/-- Bundle the actual subgroup `U` as a Sylow subgroup using split
Tits-system structure and the Borel p-subgroup criterion. -/
def sylowOfSplit [Finite G] {p : ℕ} [Fact p.Prime]
    (hU : IsPGroup p U)
    (hBmax : ∀ P : Subgroup G, P ≤ B → IsPGroup p P → P ≤ U) : Sylow p G :=
  { U with
    isPGroup' := hU
    is_maximal' := fun hP hUP =>
      h.maximalPSubgroup_of_split hUB hBU hsplit hBmax _ hUP hP }

@[simp] theorem sylowOfSplit_toSubgroup [Finite G] {p : ℕ} [Fact p.Prime]
    (hU : IsPGroup p U)
    (hBmax : ∀ P : Subgroup G, P ≤ B → IsPGroup p P → P ≤ U) :
    (h.sylowOfSplit hUB hBU hsplit hU hBmax).toSubgroup = U := rfl

end IsTitsSystem

end Langlands.Group
