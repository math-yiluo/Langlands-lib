# Coordinates of uniform source refinements

Author: Worker 167.

This internal supporting module describes the actual permutation on source
refinement pieces and the ordered positions of their target blocks. All
declarations are in `Langlands.Classification.ShuffleRefinement`.

Fix an arbitrary field `K`, natural numbers `m` and `r`, `hr : 0 < r`, an
ordered shape `B : BlockShape (m * r)`, an actual coordinate permutation `w`,
and a refinement `S : BlockRefinement B`. Write `C = BlockShape.uniform m r hr`.
The hypotheses used below are explicitly supplied:
`hS : sourceLevi K B C w = refinedLevi K B S` and
`hw : IsMinimalRepresentative B C w`. Divisibility of refinement sizes is an
additional explicit input wherever stated. The field universe is arbitrary;
there is no assumption that `m` is positive. Zero total rank has empty block
index types.

`refinementTargetIndex hr B w S j i` is the target block label of the image
under `w` of the first coordinate of refinement piece `i` in source block `j`.
The first coordinate exists because each block shape has positive sizes.
The same-block criterion from `hS` proves
`refinementTargetIndex_injective` for each fixed `j`: equality of these target
labels forces equality of refinement-piece labels. This lemma needs no
minimality or divisibility.

For one piece with `hi : r ∣ (S j).size i`, the earlier finite refinement
module gives `(S j).size i = r` and surjectivity of its coordinate embedding
onto the containing target block. In `source_piece_coordinates`, source
minimality makes the restriction of `w` to this piece strictly increasing.
The target block embedding, after the finite cast justified by the size
equality, is also strictly increasing. Surjectivity identifies their ranges.
Uniqueness of strictly increasing functions with the same range proves the
actual coordinate equality

```text
w (B.index j ((S j).index i a)) =
  C.index (refinementTargetIndex hr B w S j i) (Fin.cast size_equality a).
```

`inverse_source_piece_coordinates` applies `w.symm` to this equality.
`refinementTargetIndex_label` specializes the inverse equality to coordinate
zero and takes its original source block label. Thus the target block's
`targetBlockLabel` is exactly `j`. This conclusion uses divisibility only
for the selected piece.

`refinementTargetIndex_strictMono` uses the ordering of distinct refinement
pieces, forward source minimality, and monotonicity of target block labels.
Together with injectivity, the resulting monotonicity is strict.

`sourceTargetBlocks hr B w j` is the finite set of target blocks whose inverse
source label is `j`. Suppose now that every source refinement size is
divisible by `r`. Then `inverse_same_source_block` supplies whole-target
containment. The label-cardinality theorem gives
`(sourceTargetBlocks hr B w j).card * r = B.size j`. Summing the refinement
sizes, each equal to `r`, gives the same expression with `(S j).length`.
Cancellation by positive `r` proves `card_sourceTargetBlocks`:

```text
(sourceTargetBlocks hr B w j).card = (S j).length.
```

The target indices all belong to this finite set and are strictly increasing.
Mathlib's uniqueness of the increasing finite enumeration therefore proves
`refinementTargetIndex_eq_orderEmbOfFin`. Finally,
`card_sourceTargetBlocks_before` identifies the target blocks strictly below
the target index of piece `i` with the image of `Finset.Iio i` under that
increasing embedding. Injectivity preserves cardinality, and
`Fin.card_Iio` gives

```text
((sourceTargetBlocks hr B w j).filter
  (· < refinementTargetIndex hr B w S j i)).card = i.val.
```

This is the finite count of earlier positions of the same source run. No
exponent function or representation is identified in this module.

The provenance is internal. The module cites no original literature; its
proofs use actual finite block coordinates, equality of increasing maps with
equal ranges, and finite cardinalities. Its principal proved inputs are:

| Input | Module and originating task | Role and independence |
| --- | --- | --- |
| `source_size_eq_of_dvd`, `sourceBlockEmbedding_surjective`, `inverse_same_source_block` | `UniformRefinementCombinatorics`, task `0c90f7e4-78fa-43fd-8736-238bb3e8617d` | Finite size and surjectivity consequences of the explicit intersection equality and divisibility; no segment Jacquet theorem is assumed. |
| `targetBlockLabel_card` and the whole-target interfaces | `UniformTargetBlockLabels`, task `0c90f7e4-78fa-43fd-8736-238bb3e8617d` | Counts actual uniform target labels through finite coordinate equivalences. This separately submitted pair must be published before integration of the present module. |
| `SegmentEdge.sameBlock_of_sourceLevi_eq` | `SegmentEdgeCombinatorics`, task `b331611c-526d-4925-87fe-ea67ed6e6fed` | Transposition-matrix test for source intersections, used only as a finite block-label equivalence. The task's full segment Jacquet theorem is not assumed. |
| `exists_index_of_blockIndex_eq` | `WeylUniquenessProof`, task `9ad51693-f8a1-45de-949a-72d07ecc13b9` | Recovers a coordinate in its specified target block. |
| `index_strictMono` and `blockIndex_monotone` | `WeylMinimalRepresentativeProof`, task `6e35399b-9029-438e-9663-5ce96ab02576` | Orders actual consecutive block coordinates. |
| `blockIndex_index` and `BlockShape.index_lt_index_of_block_lt` | Existing `WeylDefinitions` and `Blocks` infrastructure | Coordinate inverse laws and ordering of distinct consecutive blocks. |
| `StrictMono.eq_of_range_eq`, `Finset.orderEmbOfFin_unique`, `Finset.range_orderEmbOfFin`, and `Fin.card_Iio` | Mathlib | Uniqueness, increasing finite enumeration, and the size of a strict initial interval. |

The recursive project import closure has 79 modules. Its classification
modules are exactly `ConstituentRelations`, `SegmentEdgeCombinatorics`,
`Segments`, `Supercuspidal`, `SupercuspidalTwist`,
`UniformRefinementCombinatorics`, and `UniformTargetBlockLabels`. These and
the remaining lower block, matrix, twist, filtration-definition and
representation infrastructure contain none of the parent's excluded
classification, irreducibility criterion, commutation, gluing, exhaustion,
quotient-Hom, or derivative inputs. The import audit is transitive.

The source intersection equality, minimality, and stated divisibility remain
hypotheses. The module proves no geometric-lemma filtration, vanishing of
other pieces, representation equivalence, segment Jacquet formula, or shuffle
Jacquet formula. In particular it does not prove the unconditional parent
`JuxtaposedSegmentSocleReverseProductStructure`.
