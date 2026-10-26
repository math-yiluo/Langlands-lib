# Actual blocks in fixed-rank segment replacements

Author: Worker 494.

This internal construction packages segment occurrences with their supplied
actual representations. `SegmentBlock T` is the dependent pair of a segment
`Δ` and a smooth complex representation of `GL_(Δ.degree)(F)`. Its carrier
universe is `max uF uV`; the field and segment-base universes stay independent.
`SegmentBlock.IsSocle` is precisely the existing strong `IsSegmentSocle`
relation for that pair.

`SegmentProductDatum.blockList` lists these dependent pairs in the datum's
original order. Mapping to their first components gives the original segment
list, their degrees sum to the original rank, and their individual socle
relations hold exactly when `HasSegmentSocles` holds for the datum.

`ofBlockList` constructs an actual product datum from any list of supplied
blocks and a proof that their degrees sum to the specified rank. Its segment
and block at each finite index are the two components of the list entry.
`blockList_ofBlockList` recovers the entire dependent-pair list exactly,
so actual representations and repeated occurrences are retained.
`ofBlockList_segments` and `ofBlockList_hasSegmentSocles_iff` give the
corresponding segment-list and strong-socle properties.

For a displayed decomposition of an original block list as `s ++ a :: b :: t`,
`replacementBlockList_degree_sum` uses the existing support-certified
union/intersection degree identity. Integral twist freeness, precedence of
`a.1` before `b.1`, and exact union/intersection supports for the supplied
replacement blocks are explicit premises. It proves that
`s ++ [u] ++ I.toList ++ t` has the same total degree. Empty intersection is
omitted by the option; no segment of length zero is introduced.

`replacePair` uses that identity to construct replacement product data at
the original fixed rank. `blockList_replacePair` identifies the whole actual
block list, retaining every original outside block in its original position
relative to the prefix and suffix. `replacePair_hasSegmentSocles` requires
the original datum's block socles and the supplied replacement block socles,
and then proves the replacement datum's block socles.

The provenance is elementary assembly of the published actual product-data
and support-certified union/intersection APIs. It uses no head, analytic or
multisegment classification theorem. This module does not supply segment
socles or an induced-product embedding, equivalence or filtration. In
particular, an actual irreducible embedding into the replacement product
remains a separate representation-theoretic obligation.
