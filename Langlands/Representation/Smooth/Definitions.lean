import Mathlib.RepresentationTheory.Invariants
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Smoothness and admissibility of group representations

These definitions use algebraic representations over a commutative ring. Only the
group carries a topology; no topology is imposed on the representation space.

The source convention is Casselman, *Introduction to admissible representations
of p-adic groups*, Chapter II (June 16, 2019), Section 1, page 2.
-/

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]

/-- The submodule of vectors fixed by every element of a subgroup. This is the
existing Mathlib invariant submodule of the restricted representation. -/
noncomputable def fixedVectors (ρ : Representation R G V) (K : Subgroup G) : Submodule R V :=
  Representation.invariants (ρ.comp K.subtype)

variable [TopologicalSpace G]

/-- A vector is smooth if an open subgroup fixes it. -/
def IsSmoothVector (ρ : Representation R G V) (v : V) : Prop :=
  ∃ K : OpenSubgroup G, v ∈ fixedVectors ρ K.toSubgroup

/-- A representation is smooth if all its vectors are smooth. -/
def IsSmooth (ρ : Representation R G V) : Prop :=
  ∀ v : V, IsSmoothVector ρ v

/-- An admissible representation is smooth and has finitely generated invariant
submodules for every open subgroup, using Casselman's all-open-subgroups convention. -/
def IsAdmissible (ρ : Representation R G V) : Prop :=
  IsSmooth ρ ∧ ∀ K : OpenSubgroup G, Module.Finite R (fixedVectors ρ K.toSubgroup)

end Langlands
