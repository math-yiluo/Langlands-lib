import Langlands.Representation.Smooth.Definitions
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Analysis.Complex.Basic

/-!
# Smoothness through open stabilizers

For a representation `ρ` of a topological group `G`, `Langlands.IsSmooth ρ` (every vector is
fixed by an open subgroup) is equivalent to the openness of every stabilizer
`{g | ρ g v = v}` (`isSmooth_iff_forall_isOpen`). The stabilizer of `v` is a subgroup, and a
subgroup containing an open subgroup is open.

The Library's `isSmoothVector_iff_isOpen_stabilizer`
(`Langlands/Representation/Smooth/Transfer/StabilizerProof.lean`) is the same statement through
Mathlib's `Representation.stabilizer`; this file avoids that module.
-/

namespace Langlands

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {S : Type*}
  [AddCommGroup S] [Module ℂ S]

/-- The stabilizer of a vector, as a subgroup. -/
private def stabilizerSubgroup (ρ : Representation ℂ G S) (v : S) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' := fun {x y} (hx : ρ x v = v) (hy : ρ y v = v) => by
    show ρ (x * y) v = v
    rw [map_mul, Module.End.mul_apply, hy, hx]
  one_mem' := by simp
  inv_mem' := fun {x} (hx : ρ x v = v) => by
    show ρ x⁻¹ v = v
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul]; simp

/-- A representation of a topological group is smooth exactly when the stabilizer of every vector
is open. -/
theorem isSmooth_iff_forall_isOpen (ρ : Representation ℂ G S) :
    IsSmooth ρ ↔ ∀ v, IsOpen {g | ρ g v = v} := by
  refine forall_congr' fun v => ⟨fun ⟨K, hK⟩ => ?_, fun h => ?_⟩
  · change IsOpen (stabilizerSubgroup ρ v : Set G)
    exact Subgroup.isOpen_mono (H₁ := K.toSubgroup) (H₂ := stabilizerSubgroup ρ v)
      (fun g hg => (Representation.mem_invariants _ v).1 hK ⟨g, hg⟩) K.isOpen
  · refine ⟨⟨stabilizerSubgroup ρ v, h⟩, (Representation.mem_invariants _ v).2 fun g => ?_⟩
    exact g.2

end Langlands
