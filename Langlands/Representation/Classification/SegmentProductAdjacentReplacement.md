# Actual replacement at adjacent indices

Author: Worker 494.

This internal adapter connects the actual block-list replacement constructor
to adjacent indices in an original `SegmentProductDatum`. Field and
segment-base universes remain independent; the actual block carrier universe
is their maximum.

`blockAt d i` packages the segment occurrence at `i` with its supplied actual
representation. `blockList_getElem` recovers that dependent pair from the
block list. For a natural `j` and a proof `j + 1 < d.length`,
`blockList_adjacent_decomposition` writes the entire original block list as
its prefix of length `j`, the two indexed blocks, and the suffix after
position `j + 1`. The proof splits the list with `take_append_drop` and
expands the first two entries of the remaining suffix.

`replaceAdjacentPair` assumes integral twist freeness at the matching
universes, precedence of the two original adjacent segments, supplied
actual union and optional intersection blocks, and the exact support
replacement relation for their segment components. It applies `replacePair`
to the proved decomposition. Thus its result has the original fixed total
rank, with every outside actual block retained.

`blockList_replaceAdjacentPair` identifies the result's complete actual
block list as the original prefix, the union block, the optional
intersection block, and the original suffix. `ofFn_replaceAdjacentPair`
maps this identity to segments. Its right side is precisely
`take j ++ [U] ++ I.toList ++ drop (j + 2)` for the original segment list.
This retains order, multiplicity, and repeated segment occurrences. The
empty optional intersection contributes no block.

`replaceAdjacentPair_hasSegmentSocles` additionally assumes the original
individual block socles and the supplied replacement block socles. It
transfers the corresponding property from `replacePair`.

The provenance is elementary dependent-list assembly from
`SegmentProductReplacement`, together with standard list operations.
This adapter establishes no segment-socle existence, product embedding,
filtration, commutation, precedence ordering, or multisegment exhaustion.
The linked-reduction proof still has to construct its representation
theoretic input.
