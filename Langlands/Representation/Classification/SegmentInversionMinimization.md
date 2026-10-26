# Segment-list inversion minimization under explicit local rules

Author: Worker 494.

This internal supporting module implements a conditional combinatorial step for
actual segments. It does not establish either local rule for representation
embeddings and does not prove multisegment socle exhaustion.

`HasLocalSegmentReductions P` is a proposition about an arbitrary predicate `P`
on lists of actual segments. Its first conjunct says that swapping an adjacent
unlinked pair preserves `P`, with any prefix and suffix. Its second conjunct
says that for an adjacent pair `Δ.Precedes Γ`, a list satisfying `P` either
remains in `P` after swapping that pair or admits a replacement `U :: I.toList`
in `P`. Here `Segment.IsUnionIntersectionReplacement Δ Γ U I` requires the
actual union support and the actual intersection support, with `none` precisely
when the intersection is empty. Every outside occurrence stays in its original
order. Neither rule asserts that `P` is inhabited.

`IsSegmentInversionMinimal P l` means that `P l` holds and that the natural
number `relationInversions Segment.Precedes l` is no larger than the count of
any list satisfying `P`. `exists_segmentInversionMinimal` applies `Nat.find`
to the set of counts attained by such lists. It needs only a witness for `P`,
not finiteness of lists or of representation data.

`HasLocalSegmentReductions.unrelatedSwap_preserves` uses the published theorem
`Segment.IsLinked.precedes_or_precedes`: if neither precedence direction holds,
the pair is unlinked, and the first local rule applies. This step needs no
freeness assumption.

`IsSegmentInversionMinimal.isPrecedenceOrderedList` explicitly assumes
`CuspidalIntegralTwistFreeness.{uF,uV} F T`. The positive-base-shift API then
rules out nonempty precedence cycles. If the chosen minimum has a positive
count, `exists_adjacent_relation_of_inversions_pos` exposes a preceding pair
through swaps unrelated in both directions. The preceding lemma preserves `P`
through these swaps, and their inversion count stays fixed. The second local
rule now gives either a related swap or a union/intersection replacement.
The related swap decreases the count because freeness excludes reverse
precedence. The replacement decreases it by
`IsUnionIntersectionReplacement.inversions_replace_lt`, including when the
intersection is omitted. Either outcome contradicts minimality. The zero-count
criterion gives exactly the published `IsPrecedenceOrderedList` condition.
`HasLocalSegmentReductions.exists_ordered` combines this result with the
natural-number minimum.

The provenance is an internal derivation from the imported segment, linkage,
positive-shift, occurrence-count and exposure APIs. The module imports the
linkage orientation proof, whose proof uses only support indices and twist
composition, but imports only the statement of twist freeness and retains
freeness as an explicit premise. No segment-constituent existence, local
representation filtration, ordered strong-socle existence, special-head or
analytic classification, or exhaustion result is used. Field and segment-carrier
universes remain independent. A later application to actual product embeddings
must prove both local rules and nonemptiness separately.
