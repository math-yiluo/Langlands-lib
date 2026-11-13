# Rank-order rigidity for multisegments of a common length

This internal combinatorial module derives three consequences of the published
rank order on actual cuspidal segments. It supplies the segment-length obstruction
used in clause 3 of `Langlands.Aubert.HeadProductLeadingTermStatement`, and the
proofs use only the Library's containment counts and cuspidal contents. It does not
assert a representation-theoretic irreducibility criterion or identify an Aubert
dual.

All declarations are in
`Langlands.PadicField.TopologicalData.Multisegment`, with independent field and
carrier universes. The relation `RankLE b a` means that the two multisegments have
equal cuspidal content and every segment-containment count of `b` is at least the
corresponding count of `a`.

`eq_of_le_of_cuspidalContent_eq` says that an included submultiset with equal
cuspidal content is the whole multisegment. Write the larger multisegment as the
smaller one plus a remainder. Equality of the cardinalities of their cuspidal
contents forces the remainder's content to have cardinality zero. Every segment
has positive length, so `card_le_card_cuspidalContent` forces the remainder itself
to be empty.

`RankLE.eq_of_uniform_length` assumes every segment of `a` has length `l` and
every segment of `b` has length at most `l`. For a segment `Δ` occurring in `a`,
a containing segment of either multisegment must equal `Δ`: containment cannot
strictly enlarge a segment without increasing its length. Thus the rank-count
inequality is the multiplicity inequality for `Δ`. These inequalities show
`a ≤ b` as multisets. The preceding content lemma then gives `b = a`.

`RankLE.exists_longer_segment` is the contrapositive: if `RankLE b a`, all segments
of `a` have length `l`, and `b ≠ a`, some segment of `b` has length greater than
`l`. No positivity assumption on `l` is needed, so `l = 0` is covered.

The provenance is derived/internal. Worker 597 wrote this module in the previous
instance, in Task 5496 draft revision 1; it is submitted here unchanged. The supplied proofs do not require an
equivalence between the Library's rank order and Zelevinsky's elementary-operation
order.
