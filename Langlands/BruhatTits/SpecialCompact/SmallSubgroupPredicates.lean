import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.Bases.Basic

/-!
# Literal-intersection compact-open basis predicates

These definitions describe the topology and actual ordered multiplication of
Renard V.5.2(i)--(ii). They do not provide an arbitrary compact subgroup as a
replacement for the geometrically fixed special maximal compact subgroup.
-/

universe u

open Set Filter Topology

namespace Langlands.BruhatTits.SpecialCompact

variable {H : Type u} [Group H]

/-- The actual ordered multiplication of the three literal intersections,
with values in `K`. -/
def orderedIntersectionProduct (K M N Nbar : Subgroup H) :
    ↥(K ⊓ Nbar) × ↥(K ⊓ M) × ↥(K ⊓ N) → K :=
  fun t => ⟨(t.1 : H) * (t.2.1 : H) * (t.2.2 : H),
    K.mul_mem (K.mul_mem t.1.property.1 t.2.1.property.1) t.2.2.property.1⟩

/-- Existence and uniqueness of the ordered `Nbar`, `M`, `N` factorization
of every element of `K`, using actual multiplication. -/
def HasIwahoriIntersectionDecomposition (K M N Nbar : Subgroup H) : Prop :=
  Function.Bijective (orderedIntersectionProduct K M N Nbar)

/-- The inherited family in `M` consists exactly of the literal intersections
`K ∩ M`, viewed as subgroups of `M`. -/
def intersectionFamily (M : Subgroup H) (B : Set (Subgroup H)) :
    Set (Subgroup M) :=
  {L | ∃ K ∈ B, L = K.comap M.subtype}

variable [TopologicalSpace H]

/-- One cofinal identity-neighborhood basis of compact open subgroups of `H`,
each contained and normal in the same fixed `K0`. -/
def CompactOpenNormalBasis (K0 : Subgroup H) (B : Set (Subgroup H)) : Prop :=
  (∀ K ∈ B, K ≤ K0 ∧ (K.subgroupOf K0).Normal ∧
    IsOpen (K : Set H) ∧ IsCompact (K : Set H)) ∧
  (𝓝 (1 : H)).HasBasis (fun K : Subgroup H => K ∈ B) (fun K => (K : Set H))

/-- The literal intersections of the same basis with `M` form the inherited
compact-open normal basis relative to `K0 ∩ M`. -/
def InheritedCompactOpenNormalBasis (K0 M : Subgroup H) (B : Set (Subgroup H)) : Prop :=
  CompactOpenNormalBasis (K0.comap M.subtype) (intersectionFamily M B)

end Langlands.BruhatTits.SpecialCompact
