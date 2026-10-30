import Langlands.Group.GL.UpperBruhatFiltrationGeometryStatement
import Langlands.Group.GL.UpperBruhatBoundaryProof

/-! Finite-cell consequences of strict inversion decrease on upper Bruhat boundaries. -/

namespace Langlands.GeneralLinear

universe u

section Partition

variable {K : Type u} [Field K] {n : ℕ}

/-- Every invertible matrix belongs to an actual upper Bruhat cell. -/
theorem exists_mem_upperBruhatCell (g : GeneralLinear n K) :
    ∃ w : Equiv.Perm (Fin n), g ∈ upperBruhatCell n K w := by
  obtain ⟨a, b, w, ha, hb, hfact⟩ := fieldUpperBruhatFactorizationTheorem K n g
  exact ⟨w, a, (mem_upperTriangularSubgroup_iff a).mpr ha,
    b, (mem_upperTriangularSubgroup_iff b).mpr hb, hfact⟩

/-- Two actual upper Bruhat cells containing the same matrix have the same index. -/
theorem upperBruhatCell_index_eq {g : GeneralLinear n K} {v w : Equiv.Perm (Fin n)}
    (hv : g ∈ upperBruhatCell n K v) (hw : g ∈ upperBruhatCell n K w) : v = w := by
  apply UpperBruhatRank.perm_eq_of_count_eq
  intro i j
  have h := ((upperBruhatRankCharacterization K n v g).mp hv i j).symm.trans
    ((upperBruhatRankCharacterization K n w g).mp hw i j)
  change (UpperBruhatRank.corner i j
      (permutation n K v : Matrix (Fin n) (Fin n) K)).rank =
    (UpperBruhatRank.corner i j
      (permutation n K w : Matrix (Fin n) (Fin n) K)).rank at h
  simpa only [UpperBruhatRank.rank_corner_permutation] using h

/-- Distinct upper Bruhat cells are disjoint. -/
theorem disjoint_upperBruhatCell {v w : Equiv.Perm (Fin n)} (hvw : v ≠ w) :
    Disjoint (upperBruhatCell n K v) (upperBruhatCell n K w) :=
  Set.disjoint_left.mpr fun _ hv hw => hvw (upperBruhatCell_index_eq hv hw)

/-- The union of strictly higher cells is the complement of the layer at the given count. -/
theorem upperBruhatHigherCells_eq_compl_layer (w : Equiv.Perm (Fin n)) :
    upperBruhatHigherCells n K w =
      (upperBruhatLayerLE n K (permutationInversionCount n w))ᶜ := by
  ext g
  constructor
  · rintro ⟨v, hlt, hv⟩ ⟨t, hle, ht⟩
    have hvt := upperBruhatCell_index_eq hv ht
    subst t
    exact (not_le.mpr hlt) hle
  · intro hg
    obtain ⟨v, hv⟩ := exists_mem_upperBruhatCell g
    refine ⟨v, ?_, hv⟩
    by_contra h
    exact hg ⟨v, Nat.le_of_not_gt h, hv⟩

/-- Intersecting the specified cell neighborhood with its inversion layer recovers the cell. -/
theorem upperBruhatCellNeighborhood_inter_layer (w : Equiv.Perm (Fin n)) :
    upperBruhatCellNeighborhood n K w ∩
      upperBruhatLayerLE n K (permutationInversionCount n w) = upperBruhatCell n K w := by
  ext g
  constructor
  · rintro ⟨hg | hg, hle⟩
    · exact hg
    · rw [upperBruhatHigherCells_eq_compl_layer] at hg
      exact False.elim (hg hle)
  · intro hg
    exact ⟨Or.inl hg, w, le_rfl, hg⟩

end Partition

section Topology

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [T2Space K] {n : ℕ}

/-- A finite union of cells is closed if its set of indices contains all indices with
strictly fewer inversions than each of its members. -/
private theorem isClosed_upperBruhatCellUnion (P : Equiv.Perm (Fin n) → Prop)
    (hP : ∀ v w, permutationInversionCount n v < permutationInversionCount n w →
      P w → P v) :
    IsClosed {g : GeneralLinear n K | ∃ w, P w ∧ g ∈ upperBruhatCell n K w} := by
  classical
  have hset : {g : GeneralLinear n K | ∃ w, P w ∧ g ∈ upperBruhatCell n K w} =
      ⋃ w : {w // P w}, upperBruhatCell n K w.val := by
    ext g
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨w, hw, hg⟩ => ⟨⟨w, hw⟩, hg⟩,
      fun ⟨w, hg⟩ => ⟨w.val, w.property, hg⟩⟩
  apply isClosed_of_closure_subset
  rw [hset, closure_iUnion_of_finite]
  rintro g hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hg
  apply Set.mem_iUnion.mpr
  by_cases hgw : g ∈ upperBruhatCell n K w.val
  · exact ⟨w, hgw⟩
  · obtain ⟨v, hv, hgv⟩ := upperBruhatBoundary K n w.val ⟨hw, hgw⟩
    exact ⟨⟨v, hP v w.val hv w.property⟩, hgv⟩

/-- Every layer bounded by the numerical inversion count is closed. -/
theorem isClosed_upperBruhatLayerLE (k : ℕ) :
    IsClosed (upperBruhatLayerLE n K k) :=
  isClosed_upperBruhatCellUnion (fun w => permutationInversionCount n w ≤ k)
    (fun _ _ hlt hle => hlt.le.trans hle)

/-- Every union of cells with strictly greater inversion count is open. -/
theorem isOpen_upperBruhatHigherCells (w : Equiv.Perm (Fin n)) :
    IsOpen (upperBruhatHigherCells n K w) := by
  rw [upperBruhatHigherCells_eq_compl_layer]
  exact (isClosed_upperBruhatLayerLE _).isOpen_compl

/-- The union of a cell and all cells of strictly greater inversion count is open. -/
theorem isOpen_upperBruhatCellNeighborhood (w : Equiv.Perm (Fin n)) :
    IsOpen (upperBruhatCellNeighborhood n K w) := by
  let P : Equiv.Perm (Fin n) → Prop :=
    fun v => permutationInversionCount n v ≤ permutationInversionCount n w ∧ v ≠ w
  have hclosed := isClosed_upperBruhatCellUnion (K := K) P (by
    intro v t hvt ht
    refine ⟨hvt.le.trans ht.1, ?_⟩
    intro hvw
    subst v
    exact (not_lt_of_ge ht.1) hvt)
  have hset : upperBruhatCellNeighborhood n K w =
      {g : GeneralLinear n K | ∃ v, P v ∧ g ∈ upperBruhatCell n K v}ᶜ := by
    ext g
    constructor
    · rintro (hgw | ⟨v, hv, hgv⟩) ⟨t, ht, hgt⟩
      · exact ht.2 (upperBruhatCell_index_eq hgt hgw)
      · have hvt := upperBruhatCell_index_eq hgv hgt
        subst t
        exact (not_le.mpr hv) ht.1
    · intro hg
      obtain ⟨v, hgv⟩ := exists_mem_upperBruhatCell g
      by_cases hvw : v = w
      · subst v
        exact Or.inl hgv
      · apply Or.inr
        refine ⟨v, ?_, hgv⟩
        by_contra h
        exact hg ⟨v, ⟨Nat.le_of_not_gt h, hvw⟩, hgv⟩
  rw [hset]
  exact hclosed.isOpen_compl

/-- The actual cell is closed in its specified open neighborhood, with the subtype topology. -/
theorem isClosed_upperBruhatCell_in_neighborhood (w : Equiv.Perm (Fin n)) :
    IsClosed {g : upperBruhatCellNeighborhood n K w | g.val ∈ upperBruhatCell n K w} := by
  have hset : {g : upperBruhatCellNeighborhood n K w | g.val ∈ upperBruhatCell n K w} =
      Subtype.val ⁻¹' upperBruhatLayerLE n K (permutationInversionCount n w) := by
    ext g
    change g.val ∈ upperBruhatCell n K w ↔
      g.val ∈ upperBruhatLayerLE n K (permutationInversionCount n w)
    rw [← upperBruhatCellNeighborhood_inter_layer w]
    exact and_iff_right g.property
  rw [hset]
  exact (isClosed_upperBruhatLayerLE _).preimage continuous_subtype_val

end Topology

/-- Closed inversion layers, open higher-cell unions and cell neighborhoods, and relative
closedness of every cell in its specified neighborhood, over every Hausdorff topological field. -/
theorem upperBruhatFiltrationGeometry : UpperBruhatFiltrationGeometryStatement.{u} := by
  intro K _ _ _ _ n
  exact ⟨fun k => isClosed_upperBruhatLayerLE k,
    fun w => isOpen_upperBruhatHigherCells w,
    fun w => isOpen_upperBruhatCellNeighborhood w,
    fun w => isClosed_upperBruhatCell_in_neighborhood w⟩

end Langlands.GeneralLinear
