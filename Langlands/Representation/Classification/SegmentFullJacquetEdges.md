# Bookkeeping for the edge representations of a segment induction

Author: Worker 964.

Module `Langlands.Representation.Classification.SegmentFullJacquetEdges`,
namespace `Langlands.SegmentFullJacquet`. This is an internal helper for the proof
of `Langlands.Classification.SegmentFullJacquetFormula`. Throughout,
`β = BlockShape.uniform m r hr`.

## Block permutations

- `blockPermEquiv F m r hr`: the equivalence between the minimal
  self-conjugating permutations of `β` and the permutations of `Fin m`, given by
  `blockPerm`. `blockPerm_blockPermEquiv_symm` recovers a block permutation from
  its preimage.
- `adjacentSwap k hk`: the transposition of the blocks `k` and `k + 1`. Up to
  proof irrelevance it is the exchange in `SegmentEdge.swappedFactors`.

## Separating scalars and transports of permuted tensors

- `transport_permuted_separatingScalar`. The separating scalar acts on the
  transport by `w` of the segment tensor with factors `i ↦ ν^(e i) A` by
  `segmentScalar T ω r m (blockPerm F w * e⁻¹)`. This is
  `transport_blockTensor_blockScalarLevi`, followed by reindexing the product
  along `e`.
- `nonempty_transport_equiv_permuted`. The transport by `w` of the increasing
  segment tensor is equivalent to the segment tensor with factors
  `i ↦ ν^(g⁻¹ i) A`, where `g = blockPerm F w`. By the published
  `eq_blockPermutation_of_blockIndex`, `w` is the canonical block reordering
  `β.blockPermutation g⁻¹`. The published `blockPermutationTensorEquiv` then gives
  the equivalence. The target shape `β.permute g⁻¹` is definitionally `β`.

## Exactness of normalized Jacquet maps

These are derived from the published `normalizedJacquetMap_exact`.

- `normalizedJacquetMap_injective`: an injective intertwiner into a smooth
  representation `σ` has injective normalized Jacquet map. Complete it to a short
  exact sequence with the quotient of `σ` by the range.
- `normalizedJacquetMap_surjective`: a surjective intertwiner out of a smooth
  representation has surjective normalized Jacquet map. Complete it with the
  inclusion of the kernel (`CentralEigenspaceSplitting.subrepInclusion`).
- `normalizedJacquetMap_zero`: the normalized Jacquet map of the zero intertwiner
  is zero (`Representation.Coinvariants.hom_ext`).
