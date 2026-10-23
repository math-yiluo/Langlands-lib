import Langlands.Weil.Representation.InductionFinitenessStatements
import Langlands.Representation.Category.NormalRestrictionSemisimplicity
import Langlands.Representation.Category.FiniteIndexSemisimplicity

/-!
# Finite-index restriction preserves and reflects semisimplicity

A proof of `Langlands.Weil.RepresentationFiniteIndexRestrictionSemisimplicity`
through a normal subgroup of finite index contained in `H`: semisimplicity
descends to normal subgroups and ascends from normal subgroups of finite index.
-/

namespace Langlands.Weil

universe uG uV

namespace FiniteIndexRestrictionSemisimplicity

variable {k : Type*} [Field k] {K K' : Type*} [Monoid K] [Monoid K']
  {V : Type*} [AddCommGroup V] [Module k V]

/-- Two representations on the same space with the same image have the same
subrepresentations. -/
def subrepresentationOrderIsoOfRangeEq (ρ : Representation k K V)
    (ρ' : Representation k K' V) (h : Set.range ρ = Set.range ρ') :
    Subrepresentation ρ ≃o Subrepresentation ρ' where
  toFun W := ⟨W.toSubmodule, fun x v hv => by
    obtain ⟨y, hy⟩ : ρ' x ∈ Set.range ρ := by rw [h]; exact Set.mem_range_self x
    rw [← hy]
    exact W.apply_mem_toSubmodule y hv⟩
  invFun W := ⟨W.toSubmodule, fun x v hv => by
    obtain ⟨y, hy⟩ : ρ x ∈ Set.range ρ' := by rw [← h]; exact Set.mem_range_self x
    rw [← hy]
    exact W.apply_mem_toSubmodule y hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Two representations on the same space with the same image are
simultaneously semisimple. -/
theorem isSemisimpleRepresentation_iff_of_range_eq (ρ : Representation k K V)
    (ρ' : Representation k K' V) (h : Set.range ρ = Set.range ρ') :
    Representation.IsSemisimpleRepresentation ρ ↔
      Representation.IsSemisimpleRepresentation ρ' :=
  (subrepresentationOrderIsoOfRangeEq ρ ρ' h).complementedLattice_iff

/-- For `N ≤ H`, restricting first to `H` and then to `N.subgroupOf H` has the
same image as restricting directly to `N`. -/
theorem range_comp_subgroupOf_subtype {G : Type*} [Group G]
    (σ : Representation k G V) {N H : Subgroup G} (hNH : N ≤ H) :
    Set.range ((σ.comp H.subtype).comp (N.subgroupOf H).subtype) =
      Set.range (σ.comp N.subtype) := by
  ext T
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨((x : H) : G), Subgroup.mem_subgroupOf.1 x.2⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨⟨x, hNH x.2⟩, Subgroup.mem_subgroupOf.2 x.2⟩, rfl⟩

end FiniteIndexRestrictionSemisimplicity

open FiniteIndexRestrictionSemisimplicity in
/-- Restriction of a finite-dimensional complex representation to a subgroup of
finite index, not necessarily normal, preserves and reflects semisimplicity. -/
theorem representationFiniteIndexRestrictionSemisimplicity :
    RepresentationFiniteIndexRestrictionSemisimplicity.{uG, uV} := by
  intro G _ H _ V _ _ _ σ
  -- A normal subgroup `N` of finite index in `G` contained in `H`: the normal core.
  obtain ⟨N, hNnormal, hNindex, hNH⟩ :
      ∃ N : Subgroup G, N.Normal ∧ N.FiniteIndex ∧ N ≤ H :=
    ⟨H.normalCore, inferInstance, inferInstance, H.normalCore_le⟩
  -- Its trace `N.subgroupOf H` is normal and of finite index in `H`; restricting
  -- through it agrees with restricting to `N`.
  have hN : Representation.IsSemisimpleRepresentation
        ((σ.comp H.subtype).comp (N.subgroupOf H).subtype) ↔
      Representation.IsSemisimpleRepresentation (σ.comp N.subtype) :=
    isSemisimpleRepresentation_iff_of_range_eq _ _ (range_comp_subgroupOf_subtype σ hNH)
  constructor
  · -- Descend from `H` to `N.subgroupOf H`, then ascend from `N` to `G`.
    intro hH
    exact finiteIndexSemisimplicityAscent ℂ G V N σ
      (hN.1 (finiteDimensionalNormalRestrictionSemisimplicity ℂ H V (N.subgroupOf H)
        (σ.comp H.subtype) hH))
  · -- Descend from `G` to `N`, then ascend from `N.subgroupOf H` to `H`.
    intro hG
    exact finiteIndexSemisimplicityAscent ℂ H V (N.subgroupOf H) (σ.comp H.subtype)
      (hN.2 (finiteDimensionalNormalRestrictionSemisimplicity ℂ G V N σ hG))

end Langlands.Weil
