import Langlands.Analysis.Local.QuotientMeasure
import Langlands.Representation.Induction.Definitions
import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# Topology of the actual left-coset quotient

The quotient by `QuotientGroup.rightRel H` is the orbit space of left
multiplication by `H`, so Mathlib's orbit-space theorems apply directly.
-/

namespace Langlands.QuotientIntegration

universe uG

variable {G : Type uG} [Group G]

/-- The existing canonical projection from the group onto its left cosets. -/
abbrev leftQuotientMap (H : Subgroup G) (g : G) : LeftQuotient H :=
  Langlands.Induction.quotientMap H g

@[simp] theorem leftQuotientMap_apply (H : Subgroup G) (g : G) :
    leftQuotientMap H g = Quotient.mk (QuotientGroup.rightRel H) g := rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The projection to left cosets is an open quotient map. -/
theorem leftQuotient_isOpenQuotientMap (H : Subgroup G) :
    IsOpenQuotientMap (leftQuotientMap H) :=
  MulAction.isOpenQuotientMap_quotientMk

/-- Left cosets of a closed subgroup form a Hausdorff space. -/
theorem leftQuotient_t2Space (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    T2Space (LeftQuotient H) := by
  let : IsClosed (H : Set G) := hH
  exact t2Space_quotient_mulAction_of_properSMul

/-- The left quotient of a locally compact group is locally compact. -/
theorem leftQuotient_locallyCompactSpace [LocallyCompactSpace G] (H : Subgroup G) :
    LocallyCompactSpace (LeftQuotient H) :=
  (leftQuotient_isOpenQuotientMap H).locallyCompactSpace

/-- Every compact set of left cosets is the image of a compact set in the group. -/
theorem leftQuotient_exists_isCompact_image [LocallyCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    {K : Set (LeftQuotient H)} (hK : IsCompact K) :
    ∃ C : Set G, IsCompact C ∧ leftQuotientMap H '' C = K := by
  classical
  let := leftQuotient_t2Space H hH
  let q : G → LeftQuotient H := leftQuotientMap H
  have hq : IsOpenQuotientMap q := leftQuotient_isOpenQuotientMap H
  choose r hr using hq.surjective
  choose C hCc hCr using fun x : LeftQuotient H => exists_compact_mem_nhds (r x)
  have hCn (x : LeftQuotient H) : q '' C x ∈ nhds x := by
    simpa only [hr x] using hq.isOpenMap.image_mem_nhds (hCr x)
  obtain ⟨I, _, hI⟩ := hK.elim_nhds_subcover (fun x => q '' C x) (fun x _ => hCn x)
  let L : Set G := ⋃ x ∈ I, C x
  have hLc : IsCompact L := I.isCompact_biUnion (fun x _ => hCc x)
  have hKL : K ⊆ q '' L := by
    simpa only [L, Set.image_iUnion] using hI
  refine ⟨q ⁻¹' K ∩ L, hLc.inter_left (hK.isClosed.preimage hq.continuous), ?_⟩
  exact (Set.image_preimage_inter q L K).trans (Set.inter_eq_left.mpr hKL)

end Langlands.QuotientIntegration
