# Actual union/intersection segments and degree preservation

Author: Worker 494.

This internal combinatorial unit concerns a preceding pair of segments on
an integral cuspidal twist line. Integral twist freeness is an explicit
premise at the same independent field and carrier universes as the segments.
The module imports its proposition, without using its proof or any
representation classification theorem.

`HasIntegralCoordinates.rank_eq` identifies the common general-linear rank
along the twist line. `HasIntegralCoordinates.support_inter_eq_empty` proves
that separated integral intervals have disjoint supports: a putative common
member gives equal twist indices by freeness, contradicting the endpoint gap.

`exists_unionIntersectionReplacement` uses the first segment's own integral
coordinates and transports the second segment to that line using precedence.
The existing endpoint characterization gives `a < c ≤ b + 1` and `b < d`.
The actual segment on `[a,d]` realizes the union. If `c ≤ b`, the actual
segment on `[c,b]` realizes the intersection; otherwise the intersection
is empty and is represented by `none`. In particular, a juxtaposed pair
has no artificial segment of length zero.

`IsUnionIntersectionReplacement.length_sum` applies to every replacement
with the specified actual support equalities, not just the constructed one.
The existing coordinate uniqueness theorem recovers the same endpoints.
For a nonempty intersection the identity is integral interval arithmetic.
For an omitted intersection, a common member at `c` would contradict
emptiness if `c ≤ b`, so the precedence endpoint bounds force `c = b + 1`.
The same arithmetic then proves the length identity.

`IsUnionIntersectionReplacement.degree_sum` multiplies that identity by
the common cuspidal rank. Thus the degree of the union plus the degree
sum of the optional intersection equals the original pair's degree.
`unionIntersectionPair` chooses a pair from the proved existence result,
and `unionIntersectionPair_spec` certifies its exact support equalities.
The choice is not asserted to be canonical.
`IsUnionIntersectionReplacement.degree_sum_append` preserves the degree
of a full list with arbitrary prefixes and suffixes, including repeated
segment occurrences.

This is derived bookkeeping for the linked-segment replacement interface.
Its provenance is the published actual segment, integral-coordinate and
support definitions, together with elementary integer and natural-number
arithmetic. It supplies no segment socles, no segment-product filtration,
no product equivalence, and no representation embedding or exhaustion.
The degree identity supports future construction of replacement product
data at the same fixed rank; it does not construct those actual blocks.
