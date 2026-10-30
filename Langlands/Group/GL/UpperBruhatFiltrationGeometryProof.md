# Closed inversion layers and open cell neighborhoods: proof

Author: Worker 176.

`Langlands.GeneralLinear.upperBruhatFiltrationGeometry.{u}` in
`Langlands.Group.GL.UpperBruhatFiltrationGeometryProof` proves exactly the
published proposition
`Langlands.GeneralLinear.UpperBruhatFiltrationGeometryStatement.{u}`:

```text
∀ (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [T2Space K] (n : ℕ),
  (∀ k : ℕ, IsClosed (upperBruhatLayerLE n K k)) ∧
    (∀ w : Equiv.Perm (Fin n), IsOpen (upperBruhatHigherCells n K w)) ∧
    (∀ w : Equiv.Perm (Fin n), IsOpen (upperBruhatCellNeighborhood n K w)) ∧
    ∀ w : Equiv.Perm (Fin n),
      IsClosed {g : upperBruhatCellNeighborhood n K w | g.val ∈ upperBruhatCell n K w}
```

All quantifiers are inside the proposition. The closing theorem has no caller
hypotheses. It preserves every field universe, every Hausdorff topological
division ring structure on that field, every natural rank including zero, every
natural layer bound, and every permutation. The target Lean/Markdown pair and
all imported pairs are unchanged.

The cells and their inversion count are the actual definitions in
`Langlands.Group.GL.UpperBruhatCells` and
`Langlands.Group.GL.UpperBruhatFiltration`. In the explanation below, `C_w`
denotes `upperBruhatCell n K w` and `ℓ(w)` denotes
`permutationInversionCount n w`. Thus the layer at `k` is the union of cells
with `ℓ(w) ≤ k`, the higher-cell union for `w` consists of cells with
`ℓ(v) > ℓ(w)`, and the specified neighborhood is `C_w` union that higher-cell
union.

The ambient topology throughout is the existing topology on
`Langlands.GeneralLinear n K`, the units of the matrix ring. In the final
clause, the neighborhood is a subtype with its inherited topology. The proof
uses the continuous subtype inclusion into that same ambient group.

## Published mathematical inputs

- `upperBruhatBoundary` from
  `Langlands.Group.GL.UpperBruhatBoundaryProof` places every point of
  `closure C_w \ C_w` in an actual cell `C_v` with `ℓ(v) < ℓ(w)`.
- `fieldUpperBruhatFactorizationTheorem` from
  `Langlands.Group.GL.UpperBruhatProof` factors each matrix unit as
  `a * permutation n K w * b` with upper triangular units `a` and `b`.
- `upperBruhatRankCharacterization` from
  `Langlands.Group.GL.UpperBruhatRankProof` characterizes membership in `C_w`
  by the ranks of all padded lower-left corners.
- In the same module, `UpperBruhatRank.rank_corner_permutation` identifies
  permutation-corner ranks with `UpperBruhatRank.count`, and
  `UpperBruhatRank.perm_eq_of_count_eq` proves that these counts determine a
  permutation.

These are imported published results. The proof supplies all the finite-union
and partition arguments it needs; it does not assume any geometry statement
from its caller.

## Partition and set identities

The first section needs only a field, with no topology.

`exists_mem_upperBruhatCell` turns the published factorization into actual
cell membership, using `mem_upperTriangularSubgroup_iff` for the two factors.
Consequently the cells cover the entire group.

`upperBruhatCell_index_eq` proves that if `g` belongs to both `C_v` and
`C_w`, then `v = w`. The rank characterization equates each corner rank of
`g` with the corresponding permutation-corner rank for each index. Rewriting
both permutation ranks by `rank_corner_permutation` gives equality of the
entire count profiles. The published `perm_eq_of_count_eq` then gives equality
of the indices. `disjoint_upperBruhatCell` packages this as disjointness of
the cells for distinct indices.

`upperBruhatHigherCells_eq_compl_layer` proves

```text
upperBruhatHigherCells n K w = (upperBruhatLayerLE n K ℓ(w))ᶜ.
```

A point cannot belong both to a strictly higher cell and to a cell of count at
most `ℓ(w)`: index uniqueness would give contradictory bounds on the same
count. Conversely, coverage places a point outside the layer in some cell.
Its count must exceed `ℓ(w)`, since otherwise the point would lie in the layer.

`upperBruhatCellNeighborhood_inter_layer` proves

```text
upperBruhatCellNeighborhood n K w ∩ upperBruhatLayerLE n K ℓ(w) = C_w.
```

Inside the neighborhood, a point belongs either to `C_w` or to the higher-cell
union. The latter is excluded by membership in the layer. Every point of `C_w`
belongs to the layer by its own index.

## Closed finite unions and open neighborhoods

The private lemma `isClosed_upperBruhatCellUnion` considers a predicate `P` on
the permutation indices. Its explicit condition is that `P w` and
`ℓ(v) < ℓ(w)` imply `P v`. It proves that the union of cells with index
satisfying `P` is closed.

The index subtype `{w // P w}` is finite, since permutations of `Fin n` form a
finite type. `closure_iUnion_of_finite` writes the closure of that union as
the union of the cell closures. A point in `closure C_w` either lies in `C_w`
itself, or is a boundary point. In the first case its index already satisfies
`P`. In the second, `upperBruhatBoundary` gives a cell with strictly smaller
count, and the condition on `P` includes that cell as well. Thus the closure
is contained in the original union, proving closedness.

`isClosed_upperBruhatLayerLE` applies this lemma to `P w := ℓ(w) ≤ k`.
Transitivity of the numerical bounds supplies the required condition.
`isOpen_upperBruhatHigherCells` then takes the complement of the closed layer
using the preceding complement identity.

For `isOpen_upperBruhatCellNeighborhood`, fix `w` and use

```text
P v := ℓ(v) ≤ ℓ(w) ∧ v ≠ w.
```

This predicate also satisfies the condition: if `ℓ(v) < ℓ(t) ≤ ℓ(w)`, then
`ℓ(v) ≤ ℓ(w)` and `v` cannot equal `w`. Hence the union of those cells is
closed. It is exactly the complement of the specified neighborhood. To prove
this identity, use index uniqueness to exclude an intersection with `C_w` or
with any strictly higher cell. For the converse, coverage gives a cell index;
it is either `w`, or its count must be strictly larger than `ℓ(w)` to avoid
the closed union. Taking the complement proves openness.

## Relative closedness and final assembly

`isClosed_upperBruhatCell_in_neighborhood` identifies the subset of the
neighborhood consisting of points of `C_w` with the inverse image of the
closed layer at `ℓ(w)` under `Subtype.val`. This is precisely the neighborhood
intersection identity above, applied to the underlying point of the subtype.
The map `Subtype.val` is continuous in the inherited topology, so this inverse
image is closed.

Finally, `upperBruhatFiltrationGeometry` introduces the field, all required
instances and the rank, and assembles the four preceding theorems in the
published order. None of the arguments needs `n > 0`. Finiteness, the
factorization and rank-profile facts, and the boundary theorem all include
rank zero.

## Provenance and scope

This is an internal deduction from the published mathematical inputs and
Mathlib's finite-closure and subtype-topology facts. No unpublished draft or
external literature proof is used. The target statement's Markdown explains
its motivation from Shalika's local-field dimension filtration. The present
proof instead uses the published numerical boundary containment over arbitrary
Hausdorff topological fields. It proves the four stated conclusions without
asserting a dimension formula, an analytic submanifold structure, a closure
equality, or a coordinate homeomorphism.
