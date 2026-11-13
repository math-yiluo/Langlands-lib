import Langlands.GroupTheory.ProPTransport

/-! # Inverse images of p-subgroups under maps with pro-p kernels -/

noncomputable section

universe u v

namespace Langlands.Cohomology

variable {G : Type u} [Group G] [TopologicalSpace G]
  {Q : Type v} [Group Q]

/-- A compact totally disconnected inverse image of a p-subgroup is pro-p
if the kernel is pro-p. No topology on the target is needed. -/
theorem IsProPSubgroup.comap_of_isPGroup {p : ℕ} {f : G →* Q}
    (hker : IsProPSubgroup p f.ker) (P : Subgroup Q) (hP : IsPGroup p P)
    [CompactSpace (P.comap f)] [TotallyDisconnectedSpace (P.comap f)] :
    IsProPSubgroup p (P.comap f) := by
  let r := f.subgroupComap P
  have hrker : r.ker = f.ker.subgroupOf (P.comap f) := by
    ext x
    change (⟨f x.val, x.property⟩ : P) = 1 ↔ f x.val = 1
    exact Subtype.ext_iff
  have hk : IsProPSubgroup p r.ker := by
    rw [hrker]
    exact hker.subgroupOf (f.ker_le_comap P)
  have hq : IsPGroup p ((P.comap f) ⧸ r.ker) :=
    (hP.to_subgroup r.range).of_equiv (QuotientGroup.quotientKerEquivRange r).symm
  exact IsProPSubgroup.of_isPGroup_quotient r.ker hk hq

variable [TopologicalSpace Q] [DiscreteTopology Q]

/-- The inverse image of any subgroup of a discrete group is an open subgroup
when the homomorphism is continuous. -/
def discretePreimageOpenSubgroup (f : G →* Q) (hf : Continuous f)
    (P : Subgroup Q) : OpenSubgroup G where
  toSubgroup := P.comap f
  isOpen' := (isOpen_discrete (P : Set Q)).preimage hf

@[simp]
theorem discretePreimageOpenSubgroup_toSubgroup (f : G →* Q) (hf : Continuous f)
    (P : Subgroup Q) :
    (discretePreimageOpenSubgroup f hf P).toSubgroup = P.comap f := rfl

/-- In a compact totally disconnected topological group, every inverse image
of a discrete p-subgroup is open and pro-p if the kernel is pro-p. -/
theorem IsProPSubgroup.isOpen_and_comap_of_isPGroup
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    {p : ℕ} {f : G →* Q} (hker : IsProPSubgroup p f.ker)
    (hf : Continuous f) (P : Subgroup Q) (hP : IsPGroup p P) :
    IsOpen (P.comap f : Set G) ∧ IsProPSubgroup p (P.comap f) := by
  have hopen := (discretePreimageOpenSubgroup f hf P).isOpen
  let : CompactSpace (P.comap f) :=
    isCompact_iff_compactSpace.mp
      (Subgroup.isClosed_of_isOpen (P.comap f) hopen).isCompact
  exact ⟨hopen, hker.comap_of_isPGroup P hP⟩

end Langlands.Cohomology
