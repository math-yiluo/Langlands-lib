# Actual field comparisons between supplied Borel charts

This is a derived construction using the actual supplied-torus and Borel
charts, arbitrary pullback coherence, and
`basedCoordinateIsoOfBorelCompatibleFieldIso`. It asserts no additional
source theorem.

A model's full root datum realizes its normalized inclusion at every
supplied field point: use that point's own coefficient map and the model's
fibrewise realization. The same inclusion remains maximal there. Fixed
integer cocharacter exponents retain their coordinates under arbitrary
scheme pullback.

The actual Borel inclusion in a model, followed by the model's ambient
identification on a common scheme, has the same range as the direct
pullback of the original supplied Borel. Its dynamic presentation persists
after every further pullback of the adapted open chart, by actual
cocharacter and inclusion pullback coherence.

`groupComparison` and `torusComparison` compare two charts through the
same supplied ambient group and supplied torus. Their exact inclusion
square follows from the two original squares. Their dynamic parabolics
agree under the actual ambient isomorphism because both are the pullback
of the same supplied Borel, on every test scheme.

At any common supplied field point, `basedComparison` applies the existing
field comparison constructor to these actual maps and equality, the full
realizations and maximality, and the regularity and sign data retained in
the two adapted charts. It produces a full based coordinate root-datum
comparison and its all-test character formula; no such comparison is
assumed as an extra hypothesis. The actual normalized maps to the same supplied quotient intertwine under
this torus comparison. Full fppf quotient cancellation and the two exact
simple-root projection equations therefore identify the actual field
quotient-chart transition with the derived simple-root permutation. This
pair does not yet extend transitions to open overlaps or assemble the
permutation atlas.
