# Endpoint geometry for neighboring Speh products

These internal lemmas implement the endpoint part of Badulescu (2014), proof of
Theorem 1(b)(ii). They derive facts directly from the Library's containment-count
rank order, rather than assuming a correspondence with elementary operations.
Every segment in the original multisegment is contained in some segment of a
rank-lower multisegment. Beginning and ending occurrence bounds then force the
segment at a unique greatest ending to contain the original segment at that
ending. Inclusion moves its beginning leftwards. If the original beginning has
index strictly below an exceptional largest beginning, the lower segment also
has beginning index strictly below that largest index.

The final counting lemma expresses strictly decreasing beginnings by positive
real twists. It extracts their natural indices and embeds the chain indices
into `Fin l`, proving that a chain whose first beginning avoids the exceptional
largest index has length at most `l`.

An original greatest ending persists under rank lowering: a containing segment
must end at or after that point, and the inherited ending bound forces equality.
For a decomposition into unselected and selected segments, the final endpoint
lemma analyzes actual right truncation `Multisegment.dropLast` of the selected
part. If its selected endings have positive indices at most `l` and include a
unique greatest ending, the resulting multisegment has all ending indices
strictly less than `l`. The unselected part has no greatest ending because its
occurrence was selected, and surviving truncations move their endings back by
one. This uses the published right truncation and its ending identity.

The statements retain arbitrary actual cuspidal data and real line offsets.
They do not assert MW algorithm correctness or any result about the subsequent
recursive output. They are derived combinatorial interfaces for the neighboring
Speh proof.
