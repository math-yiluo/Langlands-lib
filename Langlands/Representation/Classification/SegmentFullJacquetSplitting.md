# The full cuspidal Jacquet module of a segment induction, split by a central element

Author: Worker 964.

Module `Langlands.Representation.Classification.SegmentFullJacquetSplitting`,
namespace `Langlands.SegmentFullJacquet`. This is an internal helper for the proof
of `Langlands.Classification.SegmentFullJacquetFormula`. Throughout,
`β = BlockShape.uniform m r hr` is the shape `(r, …, r)` with `m` blocks.

## Block permutations

- `blockPerm F w`: the block map `blockMap β β w` of a minimal self-conjugating
  permutation `w`, as a permutation of `Fin m`. It is bijective by
  `TotalConjugatingCount.blockMap_bijective`.
- `blockPerm_injective`: by `TotalConjugatingCount.eq_of_blockValue_eq`, a minimal
  conjugating permutation is determined by its block map.
- `blockPerm_surjective`: for a permutation `g` of the blocks,
  `β.blockPermutation g⁻¹` is minimal and conjugates `β.permute g⁻¹ = β` to itself
  (`isMinimalRepresentative_blockPermutation`, `conjugatesLevi_blockPermutation`).
  Its block map is `g` (`blockIndex_blockPermutation`).
- `isMinimalRepresentative_adjacentMerge_iff`. Let `w` be a minimal
  self-conjugating permutation of `β`. Then `w` is also minimal for
  `(β.adjacentMerge k hk, β)` exactly when `blockPerm w k < blockPerm w (k + 1)`.
  The proof uses `isMinimalRepresentative_iff`, `blockIndex_adjacentMerge` and
  `adjacentCollapse_eq_iff`. Two coordinates are in the same merged block when they
  are in the same block of `β`, or in the blocks `k` and `k + 1`. A permutation that
  preserves blocks preserves the order of coordinates in different blocks exactly
  according to the order of the blocks (`Geometric.blockIndex_monotone`).

## The separating scalar

- `separatingScalar F T m r hr` is the block scalar `β.blockScalarLevi` with
  entries `separatingEntries T m`, that is `diag(ϖ^(m^0) I_r, …, ϖ^(m^(m-1)) I_r)`.
  It is central in the Levi (`separatingScalar_comm`, from `scalarToCenter`).
- `transport_segment_separatingScalar`: on the transport by `w` of the increasing
  segment tensor `A ⊗ νA ⊗ ⋯ ⊗ ν^(m-1)A`, it acts by
  `segmentScalar T ω r m (blockPerm F w)`. This is
  `transport_blockTensor_blockScalarLevi` with the scalar characters
  `hasScalarCharacter_segmentFactor` of the factors.

## The filtration

`exists_segmentJacquetFiltration` assumes the published proposition
`CuspidalSupport.AssociatedJacquetFiltrationTheorem F T (m * r)` (BZ77 2.12–2.13,
not yet proved in the Library), `0 < m`, a supercuspidal `A` of `GL_r` and a
scalar character `ω` of `A`. It produces an indexing `e` of the minimal
self-conjugating permutations and an actual filtration `s` of the normalized
Jacquet module along `β` of `T.segmentInduced A.obj m hr`, with:

- irreducible graded pieces (`s.HasSimpleFactors`);
- the separating scalar acting on the `k`-th piece by
  `segmentScalar T ω r m (blockPerm F (e k))`;
- the `k`-th piece equivalent to the transport by `e k` of the increasing segment
  tensor.

The external tensor is irreducible and Levi-cuspidal
(`segmentFactors_isIrreducible_isLeviCuspidal`), and `β` is associated with
itself (`LevisAssociated.refl`). Irreducibility of the pieces comes from
`JacquetLength.isIrreducible_transport` and `isIrreducible_iff_of_equiv`. The
scalar action is carried along the graded equivalence by
`CentralEigenspaceSplitting.apply_eq_smul_of_equiv`.
