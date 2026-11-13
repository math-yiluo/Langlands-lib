# MW length bounds for neighboring rectangles

This derived adapter connects the integer-line MW recursion
to the actual endpoint calculations in `SpehNeighborRectangleEndpoints`. Its
source is Badulescu (2014), proof of Theorem 1(b)(ii), using the algorithm and
property (P) stated earlier in the same paper.

The first interval is an input occurrence by the round partition. The descending
lexicographic sort puts its ending above every input ending. The emitted interval
has as many points as the round has selections. Realization commutes with right
shortening: a surviving integer interval and the actual segment truncation have
the same beginning and length, and singleton intervals disappear on both sides.
Multiset induction retains all repeated occurrences. The selected-list adapter
records the realized occurrences as the finite family used by the endpoint lemma.

The new round adapter starts with a realized integer multisegment which is
rank-lower than the transposed neighboring rectangles. Inherited endings and
injectivity of real cuspidal twists put its integer endings in `[0,l]`. The
greatest endpoint still occurs, so the first chosen interval ends at `l`.
The selected list realizes as an occurrence-preserving finite family. Consecutive
integer endings and strictly decreasing integer beginnings become the actual
endpoint and positive-twist hypotheses of the first-step endpoint lemma.
That lemma bounds the first emitted length by `l` and puts all residual endings
in `[0,l)`. Realization commutes with shortening, and twist injectivity transfers
these residual bounds back to integers.

`dual_lengths_le_neighbor_rectangles` assumes the explicit proposition
`EndingBound`. It uses that assumption only on the residual multisegment;
the first emitted interval is bounded by the endpoint argument just described.
The recursive dual equation separates these two cases. This conditional
theorem does not establish property (P) or the main irreducibility target.

The imported MW modules supply the concrete algorithm, realization and property
statements. This adapter supplies no proof of MW support preservation,
involutivity, property (P), or Aubert correctness.
