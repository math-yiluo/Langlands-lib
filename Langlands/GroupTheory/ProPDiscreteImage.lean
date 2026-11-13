import Langlands.Cohomology.DivisibleSystem.ProPInvariants
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Discrete images of pro-p subgroups -/

noncomputable section

universe u v

namespace Langlands.Cohomology

variable {G : Type u} [Group G] [TopologicalSpace G]
  {Q : Type v} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]

/-- The kernel of a continuous homomorphism to a discrete group, as an
open normal subgroup. -/
def discreteOpenKernel (f : G →* Q) (hf : Continuous f) :
    OpenNormalSubgroup G where
  toSubgroup := f.ker
  isOpen' := by
    change IsOpen (f ⁻¹' {1})
    exact (isOpen_discrete {1}).preimage hf
  isNormal' := inferInstance

@[simp]
theorem discreteOpenKernel_toSubgroup (f : G →* Q) (hf : Continuous f) :
    (discreteOpenKernel f hf).toSubgroup = f.ker := rfl

variable {p : ℕ} {H : Subgroup G}

/-- The range of a continuous homomorphism from a pro-p subgroup to a
discrete group is a p-group. -/
theorem IsProPSubgroup.isPGroup_range (hH : IsProPSubgroup p H)
    (f : H →* Q) (hf : Continuous f) : IsPGroup p f.range := by
  exact (hH.isPGroup (discreteOpenKernel f hf)).of_equiv
    (QuotientGroup.quotientKerEquivRange f)

/-- A surjective discrete image of a pro-p subgroup is a p-group. -/
theorem IsProPSubgroup.isPGroup_of_surjective (hH : IsProPSubgroup p H)
    (f : H →* Q) (hf : Continuous f) (hs : Function.Surjective f) :
    IsPGroup p Q := by
  exact (hH.isPGroup (discreteOpenKernel f hf)).of_equiv
    (QuotientGroup.quotientKerEquivOfSurjective f hs)

/-- The image of a pro-p subgroup under a continuous map to a discrete
group is a p-subgroup of that group. -/
theorem IsProPSubgroup.isPGroup_map (hH : IsProPSubgroup p H)
    (f : G →* Q) (hf : Continuous f) : IsPGroup p (H.map f) := by
  have hr := hH.isPGroup_range (f.comp H.subtype) (hf.comp continuous_subtype_val)
  exact hr.of_equiv (MulEquiv.subgroupCongr
    ((MonoidHom.range_comp f H.subtype).trans (congrArg (Subgroup.map f) H.range_subtype)))

/-- If a discrete group has no nontrivial p-subgroups, a continuous
homomorphism from a pro-p subgroup to it is trivial. -/
theorem IsProPSubgroup.range_eq_bot (hH : IsProPSubgroup p H)
    (f : H →* Q) (hf : Continuous f)
    (hQ : ∀ K : Subgroup Q, IsPGroup p K → K = ⊥) :
    f.range = ⊥ :=
  hQ f.range (hH.isPGroup_range f hf)

/-- A pro-p subgroup lies in the kernel of a continuous homomorphism to
a discrete group without nontrivial p-subgroups. -/
theorem IsProPSubgroup.le_ker (hH : IsProPSubgroup p H)
    (f : G →* Q) (hf : Continuous f)
    (hQ : ∀ K : Subgroup Q, IsPGroup p K → K = ⊥) :
    H ≤ f.ker := by
  intro x hx
  have hm : H.map f = ⊥ := hQ (H.map f) (hH.isPGroup_map f hf)
  have hfx : f x ∈ H.map f := ⟨x, hx, rfl⟩
  rw [hm] at hfx
  exact hfx

end Langlands.Cohomology
