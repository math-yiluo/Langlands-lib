import Langlands.GroupTheory.ProPExtension
import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Transport of pro-p subgroups through topological group isomorphisms -/

noncomputable section

universe u v

namespace Langlands.Cohomology

variable {G : Type u} [Group G] [TopologicalSpace G]
  {Q : Type v} [Group Q] [TopologicalSpace Q]

/-- A topological group isomorphism induces an order isomorphism on open normal
subgroups, by inverse image. -/
def openNormalComapOrderIso (e : G ≃ₜ* Q) :
    OpenNormalSubgroup Q ≃o OpenNormalSubgroup G where
  toFun := openNormalComap e.toMonoidHom e.continuous
  invFun := openNormalComap e.symm.toMonoidHom e.symm.continuous
  left_inv N := by
    ext x
    change e (e.symm x) ∈ N ↔ x ∈ N
    simp
  right_inv N := by
    ext x
    change e.symm (e x) ∈ N ↔ x ∈ N
    simp
  map_rel_iff' := by
    intro N M
    constructor
    · intro h x hx
      have hx' : e.symm x ∈ openNormalComap e.toMonoidHom e.continuous N := by
        change e (e.symm x) ∈ N
        simpa using hx
      have hm := h hx'
      change e (e.symm x) ∈ M at hm
      simpa using hm
    · intro h x hx
      exact h hx

@[simp]
theorem openNormalComapOrderIso_toSubgroup (e : G ≃ₜ* Q)
    (N : OpenNormalSubgroup Q) :
    (openNormalComapOrderIso e N).toSubgroup = N.toSubgroup.comap e.toMonoidHom := rfl

/-- The pro-p predicate is preserved by a topological group isomorphism of
the actual subgroup types. -/
theorem IsProPSubgroup.of_continuousMulEquiv {p : ℕ}
    {H : Subgroup G} {K : Subgroup Q} (hH : IsProPSubgroup p H)
    (e : H ≃ₜ* K) : IsProPSubgroup p K where
  prime := hH.prime
  compactSpace := by
    let := hH.compactSpace
    exact e.toHomeomorph.compactSpace
  totallyDisconnectedSpace := by
    let := hH.totallyDisconnectedSpace
    exact e.toHomeomorph.totallyDisconnectedSpace
  isPGroup N := by
    intro z
    refine Quotient.inductionOn' z ?_
    intro y
    obtain ⟨n, hn⟩ := hH.isPGroup (openNormalComapOrderIso e N)
      (QuotientGroup.mk (e.symm y))
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    have hx : e.symm y ^ p ^ n ∈ (openNormalComapOrderIso e N).toSubgroup :=
      (QuotientGroup.eq_one_iff _).mp (by
        simpa only [QuotientGroup.mk_pow] using hn)
    change e (e.symm y ^ p ^ n) ∈ N.toSubgroup at hx
    simpa only [map_pow, e.apply_symm_apply] using hx

/-- Viewing a subgroup inside a containing subgroup preserves its pro-p
property and its induced topology. -/
theorem IsProPSubgroup.subgroupOf {p : ℕ} {H K : Subgroup G}
    (hH : IsProPSubgroup p H) (hHK : H ≤ K) :
    IsProPSubgroup p (H.subgroupOf K) :=
  hH.of_continuousMulEquiv (Subgroup.subgroupOfContinuousMulEquivOfLe hHK).symm

/-- Conversely, pro-p in a containing subgroup implies pro-p in the original
ambient group. -/
theorem IsProPSubgroup.of_subgroupOf {p : ℕ} {H K : Subgroup G}
    (hH : IsProPSubgroup p (H.subgroupOf K)) (hHK : H ≤ K) :
    IsProPSubgroup p H :=
  hH.of_continuousMulEquiv (Subgroup.subgroupOfContinuousMulEquivOfLe hHK)

end Langlands.Cohomology
