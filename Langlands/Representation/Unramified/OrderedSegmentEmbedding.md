# Unlinked segment products in norm-decreasing unramified principal series

This internal specialization applies the actual unlinked embedding construction
to the Library's unramified principal series. Its norm order is decreasing,
which is the order needed for the inverse tuple in the spherical-quotient
construction. It does not prove sphericality or spherical generation.

`characterDatum` is the actual cuspidal datum of the published lifted rank-one
supercuspidal character object. `scalarUniformizerNorm_characterDatum` identifies
its scalar-uniformizer norm with the complex norm of the prescribed uniformizer
value. The scalar action of a rank-one character is the character itself; scalar
character uniqueness and the character's uniformizer formula prove the identity.

`exists_unlinked_segment_embedding` constructs an actual rank-one segment-socle
product that is irreducibly embedded in the actual normalized upper-Borel series
`principalSeriesOfTuple F z` for every weakly norm-decreasing tuple. It retains
the exact cuspidal content, all rank-one conditions, actual segment-socle proofs
and unlinkedness. A private shape adapter eliminates rank equalities and identifies
singleton target shapes with uniform shapes. The proof applies the general
unlinked embedding construction to the lifted character objects and then
transports its embedding through the tensor-induced equivalence from those
lifted lines to the scalar character model of the principal series.

`unlinkedSegmentEmbeddingDatum` chooses a datum with all those witnesses. Repeated
characters and equal norms are allowed. The field universe is arbitrary and the
cuspidal representatives are chosen on complex lines in carrier universe zero;
the actual induced representation carriers consequently have the required field
universe.
