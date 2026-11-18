import Mathlib.RepresentationTheory.Semisimple

/-! # Subrepresentations of actions with the same image -/

namespace Langlands.Weil.FiniteIndexRestrictionSemisimplicity

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

end Langlands.Weil.FiniteIndexRestrictionSemisimplicity
