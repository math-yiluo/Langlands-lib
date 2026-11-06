import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Compactness.Compact

/-! # Compactness in the norm-subgroup existence argument -/

namespace Langlands.ClassFieldTheory.Local

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The compact-subgroup criterion for a proposed norm-subgroup family. -/
def CompactNormSubgroupCriterion (𝒩 : Set (Subgroup G)) (U : Subgroup G) : Prop :=
  𝒩.Nonempty →
  (∀ N ∈ 𝒩, ∀ M ∈ 𝒩, N ⊓ M ∈ 𝒩) →
  (∀ N ∈ 𝒩, IsClosed (N : Set G)) →
  (∀ N ∈ 𝒩, N.FiniteIndex) →
  (∀ N ∈ 𝒩, ∀ H : Subgroup G, N ≤ H → H.FiniteIndex → H ∈ 𝒩) →
  IsCompact (U : Set G) →
  (∀ V : Subgroup G, U ≤ V → IsOpen (V : Set G) → V.FiniteIndex → V ∈ 𝒩) →
  ∀ H : Subgroup G, IsOpen (H : Set G) → H.FiniteIndex →
    (∀ x : G, (∀ N ∈ 𝒩, x ∈ N) → x ∈ H) → H ∈ 𝒩

omit [IsTopologicalGroup G] in
/-- A downward directed family of closed subgroups eventually meets a compact
subgroup only inside any open set containing its universal intersection. -/
theorem exists_subgroup_inf_le_of_compact
    (𝒩 : Set (Subgroup G)) (hne : 𝒩.Nonempty)
    (hdir : DirectedOn (· ≥ ·) 𝒩)
    (hclosed : ∀ N ∈ 𝒩, IsClosed (N : Set G))
    (U H : Subgroup G) (hU : IsCompact (U : Set G))
    (hH : IsOpen (H : Set G))
    (hinter : ∀ x : G, (∀ N ∈ 𝒩, x ∈ N) → x ∈ H) :
    ∃ N ∈ 𝒩, N ⊓ U ≤ H := by
  let : Nonempty 𝒩 := hne.to_subtype
  have hdisj : Disjoint ((U : Set G) \ H)
      (⋂ N : 𝒩, (N.1 : Set G)) := by
    apply Set.disjoint_left.mpr
    intro x hx hxN
    exact hx.2 (hinter x (fun N hN => Set.mem_iInter.mp hxN ⟨N, hN⟩))
  have hd : Directed (· ⊇ ·) (fun N : 𝒩 => (N.1 : Set G)) := by
    intro N M
    obtain ⟨L, hL, hLN, hLM⟩ := hdir N.1 N.2 M.1 M.2
    exact ⟨⟨L, hL⟩, hLN, hLM⟩
  obtain ⟨N, hN⟩ := (hU.diff hH).elim_directed_family_closed
    (fun N : 𝒩 => (N.1 : Set G)) (fun N => hclosed N.1 N.2) hdisj hd
  refine ⟨N.1, N.2, ?_⟩
  intro x hx
  by_contra hxH
  exact Set.disjoint_left.mp hN ⟨hx.2, hxH⟩ hx.1

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The elementary subgroup identity used after compact extraction. -/
theorem inf_sup_inf_le_of_inf_le (N U H : Subgroup G) (h : N ⊓ U ≤ H) :
    N ⊓ (U ⊔ (N ⊓ H)) ≤ H := by
  intro x hx
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hx.2
  have haN : a ∈ N := by
    have hprod : a * b ∈ N := hab ▸ hx.1
    simpa using N.mul_mem hprod (N.inv_mem hb.1)
  exact hab ▸ H.mul_mem (h ⟨haN, ha⟩) hb.2

/-- Serre's compact-subgroup criterion: a family closed under intersections and
finite-index overgroups contains every open finite-index subgroup containing
its universal intersection, provided that it contains the finite-index
overgroups of one compact subgroup. -/
theorem subgroup_mem_of_compact_universal_intersection
    (𝒩 : Set (Subgroup G)) (hne : 𝒩.Nonempty)
    (hinf : ∀ N ∈ 𝒩, ∀ M ∈ 𝒩, N ⊓ M ∈ 𝒩)
    (hclosed : ∀ N ∈ 𝒩, IsClosed (N : Set G))
    (hindex : ∀ N ∈ 𝒩, N.FiniteIndex)
    (hup : ∀ N ∈ 𝒩, ∀ H : Subgroup G, N ≤ H → H.FiniteIndex → H ∈ 𝒩)
    (U : Subgroup G) (hU : IsCompact (U : Set G))
    (hUover : ∀ V : Subgroup G, U ≤ V → IsOpen (V : Set G) →
      V.FiniteIndex → V ∈ 𝒩)
    (H : Subgroup G) (hH : IsOpen (H : Set G)) (hHindex : H.FiniteIndex)
    (hinter : ∀ x : G, (∀ N ∈ 𝒩, x ∈ N) → x ∈ H) :
    H ∈ 𝒩 := by
  have hdir : DirectedOn (· ≥ ·) 𝒩 := by
    intro N hN M hM
    exact ⟨N ⊓ M, hinf N hN M hM, inf_le_left, inf_le_right⟩
  obtain ⟨N, hN, hNU⟩ := exists_subgroup_inf_le_of_compact
    𝒩 hne hdir hclosed U H hU hH hinter
  let : N.FiniteIndex := hindex N hN
  let : H.FiniteIndex := hHindex
  have hNopen := N.isOpen_of_isClosed_of_finiteIndex (hclosed N hN)
  have hVopen : IsOpen ((U ⊔ (N ⊓ H) : Subgroup G) : Set G) :=
    Subgroup.isOpen_mono le_sup_right (hNopen.inter hH)
  have hVindex : (U ⊔ (N ⊓ H)).FiniteIndex :=
    Subgroup.finiteIndex_of_le (H := N ⊓ H) le_sup_right
  have hV := hUover (U ⊔ (N ⊓ H)) le_sup_left hVopen hVindex
  exact hup _ (hinf N hN _ hV) H (inf_sup_inf_le_of_inf_le N U H hNU) hHindex

/-- The compact-subgroup criterion holds for every family and subgroup. -/
theorem compactNormSubgroupCriterion (𝒩 : Set (Subgroup G)) (U : Subgroup G) :
    CompactNormSubgroupCriterion 𝒩 U := by
  intro hne hinf hclosed hindex hup hU hUover H hH hHindex hinter
  exact subgroup_mem_of_compact_universal_intersection
    𝒩 hne hinf hclosed hindex hup U hU hUover H hH hHindex hinter

end Langlands.ClassFieldTheory.Local
