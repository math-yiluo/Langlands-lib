# Uniform target blocks and divisible source refinements

Author: Worker 167.

This internal supporting module concerns finite coordinates of ordered block
shapes over an arbitrary field. It assumes that the source-Levi intersection of
a permutation is a specified standard refinement. It assumes no
representation-theoretic proposition.

All declarations are in `Langlands.Classification.ShuffleRefinement`. The
general construction takes a field `K`, two ordered shapes `B, C` of the same
rank, a coordinate permutation `w`, a refinement `S` of `B`, and the equality
`sourceLevi K B C w = refinedLevi K B S`. The uniform results specialize `C` to
`BlockShape.uniform m r hr`, where `hr : 0 < r`. The field universe is arbitrary,
and zero total rank is permitted when there are no blocks.

The source block embedding sends a coordinate in a block of the source
refinement through the permutation into its containing target block. The
published `SegmentEdge.sameBlock_of_sourceLevi_eq` proves membership, and the
coordinate embeddings and permutation prove injectivity. Comparing finite
cardinalities bounds the source refinement size by the containing target size.

For a uniform target of rank `r > 0`, a positive source refinement size divisible
by `r` is therefore equal to `r`. Summing these sizes computes the number of
blocks in each source refinement. Consequently the refinement of a source
block of size `q * r` is the uniform shape with `q` blocks of rank `r`, after
transport along the supplied rank equality.

Equal finite cardinalities also make each source block embedding surjective.
If all source refinement sizes are divisible by `r`, any two coordinates in one
target block have inverse images in the same original source block. The
entrywise characterization of `sourceLevi` then proves that the reverse
source-Levi intersection is the full target Levi.

The exported declarations are:

- `sourceBlockEmbedding`: the actual injection from `Fin ((S j).size i)` into
  the fiber of the target block label of the image of its first coordinate.
- `source_size_le_target`: the size of this source piece is at most the size of
  that target block.
- `source_size_eq_of_dvd`: for a uniform target, divisibility of one source
  piece's size by `r` forces its size to equal `r`.
- `source_length_of_dvd`: if `B.size j = q * r` and all pieces of `S j` have
  sizes divisible by `r`, then `(S j).length = q`.
- `source_eq_uniform_of_dvd`: under the same hypotheses, rank transport of
  `S j` is exactly `BlockShape.uniform q r hr`.
- `sourceBlockEmbedding_surjective`: divisibility for one piece makes its
  coordinate embedding surjective onto its containing target block.
- `inverse_same_source_block`: if every piece size is divisible by `r`, two
  coordinates of one uniform target block have inverse images under `w` in
  the same original block of `B`.
- `reverse_sourceLevi_eq_top`: under this global divisibility hypothesis,
  `sourceLevi K (BlockShape.uniform m r hr) B w.symm = ⊤`.

In the last proof, the entrywise description of source-Levi membership asks
for vanishing only when two inverse images have distinct source block labels.
The preceding same-block result rules out that case for every pair of entries
within a uniform block. It applies to every element of the target Levi, proving
the subgroup is full.

These conclusions isolate a finite block step in the shuffle Jacquet
calculation needed by the juxtaposed segment argument. They do not prove the
vanishing of other Jacquet pieces, enumerate surviving permutations, identify
their representations, or prove the shuffle or juxtaposed segment theorem.

The provenance is internal: the proofs use published block-coordinate
definitions, finite-cardinality comparisons, the source-intersection same-block
lemma, and the entrywise characterization of source-Levi membership. They cite
no original literature and do not invoke the geometric lemma, segment
constituent existence, segment Jacquet formulas, irreducibility criteria,
commutation, exhaustion, or derivatives.

The used Library inputs and their provenance are:

| Input | Published location and originating task | Role and independence |
| --- | --- | --- |
| `SegmentEdge.sameBlock_of_sourceLevi_eq` | `Langlands.Representation.Classification.SegmentEdgeCombinatorics`, supporting unit of task `b331611c-526d-4925-87fe-ea67ed6e6fed` | Tests a source-intersection equality with transposition matrices. Only this finite coordinate lemma is used; the task's segment Jacquet theorem is not assumed. |
| `TotalConjugatingCount.card_blockIndex_fiber` | `Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof`, task `5becc159-1242-4fa4-9102-79aa6e2726c0` | Counts coordinates by the published block-index equivalence. No representation result enters this lemma. |
| `BlockShape.rankCast` | `Langlands.Group.GL.SingleBlock`, task `7c0e046b-2807-40d0-bf95-992a26ddaa3f` | Transports only the asserted total rank, preserving ordered sizes. |
| `mem_sourceLevi_iff` | `Langlands.Representation.Geometric.StandardIntersectionsProof`, task `5f658ba6-5c6d-46e0-a5c1-6d15317f8a1d` | The matrix-entry membership criterion, independent of geometric-lemma filtration or classification conclusions. |
| Block-coordinate laws, `BlockShape.ext_of_size`, finite cardinality inequalities | Existing `Blocks`, `WeylDefinitions` and Mathlib infrastructure | Actual coordinate embeddings, shape extensionality, and injective finite-cardinality comparison. |

The recursive project import closure has 77 modules. Its classification imports
are only segment definitions, constituent-relation definitions, supercuspidal
twist infrastructure and `SegmentEdgeCombinatorics`. The rest is finite matrix,
block, normalization, twist and representation infrastructure. No excluded
classification, product criterion, commutation, exhaustion, quotient-Hom or
derivative conclusion is imported or used. The general geometric lemma, full
segment Jacquet formula, and shuffle Jacquet formula remain separate proof
obligations. This supporting definition unit does not discharge the parent's
unconditional proof target.
