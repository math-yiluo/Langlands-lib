import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionRepresentability
import Mathlib.Topology.Compactness.Compact

noncomputable section

universe u

open CategoryTheory Topology TopologicalSpace
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (X : Scheme.{u}) [CompactSpace X] (hX : HasFiniteAffineNeighborhoods X)

include hX in
private theorem exists_finite_affine_tuple_family (n : ℕ) :
    ∃ a : Finset X.affineOpens, ∀ f : Fin n → X,
      ∃ U ∈ a, ∀ i, f i ∈ U.val := by
  classical
  let V (U : X.affineOpens) : Set (Fin n → X) := {f | ∀ i, f i ∈ U.val}
  have hopen (U : X.affineOpens) : IsOpen (V U) := by
    convert isOpen_iInter_of_finite
      (fun i : Fin n => U.val.2.preimage (continuous_apply i)) using 1
    ext f
    constructor
    · intro hf
      exact Set.mem_iInter.mpr (fun i => hf i)
    · intro hf i
      exact Set.mem_iInter.mp hf i
  have hcover : (Set.univ : Set (Fin n → X)) ⊆ ⋃ U, V U := by
    intro f _
    obtain ⟨U, hU⟩ := hX (Set.range f) (Set.finite_range f)
    exact Set.mem_iUnion.mpr ⟨U, fun i => hU ⟨i, rfl⟩⟩
  obtain ⟨a, ha⟩ := isCompact_univ.elim_finite_subcover V hopen hcover
  refine ⟨a, fun f => ?_⟩
  obtain ⟨U, hUa, hUf⟩ := Set.mem_iUnion₂.mp (ha (Set.mem_univ f))
  exact ⟨U, hUa, hUf⟩

/-- A finite original affine family containing every original tuple of the specified length. -/
def affineTupleNeighborhoodFamily (n : ℕ) : Finset X.affineOpens :=
  Classical.choose (exists_finite_affine_tuple_family X hX n)

theorem affineTupleNeighborhoodFamily_covers (n : ℕ) (f : Fin n → X) :
    ∃ U ∈ affineTupleNeighborhoodFamily X hX n, ∀ i, f i ∈ U.val :=
  Classical.choose_spec (exists_finite_affine_tuple_family X hX n) f

/-- A finite family covering every tuple whose length is bounded by n, including empty tuples. -/
def boundedAffineNeighborhoodFamily (n : ℕ) : Finset X.affineOpens := by
  classical
  exact Finset.univ.biUnion fun m : Fin (n + 1) => affineTupleNeighborhoodFamily X hX m.val

/-- Every map from a finite type of cardinality at most n has its whole range in a family member. -/
theorem boundedAffineNeighborhoodFamily_covers (n : ℕ) {ι : Type u} [Finite ι]
    (hι : Nat.card ι ≤ n) (f : ι → X) :
    ∃ U ∈ boundedAffineNeighborhoodFamily X hX n, Set.range f ⊆ U.val := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hcard : Fintype.card ι < n + 1 := by
    simpa only [Nat.card_eq_fintype_card] using Nat.lt_succ_of_le hι
  let m : Fin (n + 1) := ⟨Fintype.card ι, hcard⟩
  obtain ⟨U, hU, hf⟩ := affineTupleNeighborhoodFamily_covers X hX m.val
    (fun i => f ((Fintype.equivFin ι).symm i))
  refine ⟨U, ?_, ?_⟩
  · exact Finset.mem_biUnion.mpr ⟨m, Finset.mem_univ _, hU⟩
  · rintro _ ⟨i, rfl⟩
    have hi := hf ((Fintype.equivFin ι) i)
    simp only [Equiv.symm_apply_apply] at hi
    exact hi

end Langlands.AlgebraicGeometry.PointTopology
