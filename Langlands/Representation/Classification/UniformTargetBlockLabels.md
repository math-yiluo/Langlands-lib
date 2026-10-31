# Uniform target-block labels

Author: Worker 167.

This internal supporting module parametrizes actual minimal block permutations
whose inverse sends each target block into a single source block. It uses finite
ordered coordinates only. All declarations are in
`Langlands.Classification.ShuffleRefinement`.

For arbitrary ordered block shapes `B, C : BlockShape n` and a permutation `w`,
`TargetBlocksContained B C w` means that equal target block indices imply equal
source block indices after applying `w.symm`. The function `targetBlockLabel`
records the source block of the inverse image of the first coordinate of each
target block. Positivity of block sizes provides that coordinate.
`inverse_blockIndex_eq` shows that this label applies to every coordinate in the
target block.

`range_sourceBlock` identifies the image under `w` of source block `j` with the
set of target coordinates whose target block has label `j`.
`eq_of_targetBlockLabel_eq` then shows that two minimal permutations with whole
target blocks and equal labels are equal: their strictly increasing restrictions
to each source block have equal ranges, so Mathlib's
`StrictMono.eq_of_range_eq` identifies the restrictions. Surjectivity of
`B.indexEquiv` gives equality everywhere.

The uniform section fixes `hr : 0 < r` and `B : BlockShape (m * r)`. Its target
shape is `BlockShape.uniform m r hr`. The natural number `m` may be zero; no
field, topology, representation, or positive total rank is assumed.

- `labelCoordinates hr B lab j` is the subtype of coordinates whose target
  block has label `j`.
- `labelCoordinateEquiv` identifies that subtype with
  `{i : Fin m // lab i = j} × Fin r`, using the target's block coordinate
  equivalence. Hence `card_labelCoordinates` computes its `Nat.card` as the
  label fiber cardinality times `r`.
- `LabelAssignment B` is the subtype of functions `lab : Fin m → Fin B.length`
  satisfying `Nat.card {i // lab i = j} * r = B.size j` for every source block
  `j`. It retains `m` and `r` through `B` and does not take the proof `hr` as a
  parameter.
- `WholeTargetRepresentatives hr B` is the subtype of the actual
  `MinimalRepresentatives B (BlockShape.uniform m r hr)` satisfying
  `TargetBlocksContained`.
- `targetBlockLabel_card` proves the size constraint for the labels of any such
  representative. Its inverse permutation identifies `labelCoordinates` with
  the source block fiber, whose cardinality is `B.size j`.
- `labelCoordinateOrderIso` increasingly enumerates `labelCoordinates` by
  `Fin (B.size j)`, using the cardinality constraint and
  `Fintype.orderIsoFinOfCardEq`. `labelPartitionEquiv` identifies the disjoint
  union of all these coordinate subtypes with the ambient `Fin (m * r)`.
- `permutationFromLabels` composes the source block coordinate equivalence,
  these increasing enumerations, and the partition equivalence to produce an
  actual permutation. `permutationFromLabels_index` evaluates it on a source
  block coordinate.
- `permutationFromLabels_source_strictMono` proves the source-block order
  condition. `permutationFromLabels_inverse_label` computes the source block
  index of every inverse image, and `permutationFromLabels_contained` follows.
- `permutationFromLabels_minimal` also proves the target-block order condition.
  Two increasing coordinates of a target block have inverse images in the same
  source block. The increasing enumeration of that source block and the
  increasing target coordinate embedding force the inverse images to be
  increasing as well.
- `targetBlockLabel_permutationFromLabels` recovers the supplied labels.
  Finally, `wholeTargetEquivLabels` is an equivalence between
  `WholeTargetRepresentatives hr B` and `LabelAssignment B`. Its left inverse
  uses uniqueness from equal labels; its right inverse is label recovery.

The provenance is internal. The module constructs an equivalence of explicit
finite coordinate types and proves its inverse laws. It cites no original
literature and invokes no segment Jacquet formula or geometric-lemma filtration.
The whole-target condition is an explicit hypothesis in its permutation subtype;
this module does not prove that representation-theoretic surviving terms satisfy
that condition.

The proved Library inputs actually used are:

| Input | Published module and originating task | Use and independence |
| --- | --- | --- |
| `blockIndex_index`, `BlockShape.indexEquiv` and its inverse laws | `Langlands.Representation.Geometric.WeylDefinitions` and `Langlands.Group.GL.Blocks` | Finite coordinate identification and decomposition only. |
| `exists_index_of_blockIndex_eq` | `Langlands.Representation.Geometric.WeylUniquenessProof`, task `9ad51693-f8a1-45de-949a-72d07ecc13b9` | Recovers the coordinate of a known block; proved directly with `indexEquiv`. |
| `index_strictMono` | `Langlands.Representation.Geometric.WeylMinimalRepresentativeProof`, task `6e35399b-9029-438e-9663-5ce96ab02576` | The ordered coordinate embedding, proved with the prefix-sum formula. No representation theorem enters. |
| `TotalConjugatingCount.card_blockIndex_fiber` | `Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof`, task `5becc159-1242-4fa4-9102-79aa6e2726c0` | Identifies one block fiber with `Fin (B.size j)`; no cuspidal representation theorem is used. |
| `StrictMono.eq_of_range_eq`, `Fintype.orderIsoFinOfCardEq`, equivalence and cardinality laws | Mathlib | Uniqueness of finite increasing enumerations, their existence, products and transported cardinalities. |

The recursive project import closure has 69 modules. Its classification modules
are only `Segments`, `ConstituentRelations`, `Supercuspidal`, and
`SupercuspidalTwist`; the other imports supply lower block, field, twist,
representation, and finite Weyl infrastructure. The segment module is imported
for `BlockShape.uniform`. The closure contains no excluded classification,
product irreducibility, adjacent or two-segment commutation, gluing, exhaustion,
quotient-Hom, or derivative result. In particular no exact geometric lemma,
Ze80 3.1 or 3.4 proof, or conditional segment formula is invoked.

This finite equivalence supports the remaining shuffle calculation for the
juxtaposed-segment argument. It does not identify any Jacquet representation,
prove the shuffle Jacquet formula, or prove the unconditional parent target
`JuxtaposedSegmentSocleReverseProductStructure`.
