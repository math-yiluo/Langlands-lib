# Unlinked products inside weakly ordered rank-one principal series

This internal assembly uses the published existence of an unlinked multisegment
with prescribed cuspidal content, actual segment-socle existence and
irreducibility of unlinked segment-socle products. It combines these with the
nonzero induction maps from ordered rank-one content. Sphericality and the
final spherical-generation assertion are not claimed here.

`exists_unlinked_embedding` assumes a positive number of actual rank-one
supercuspidal factors and weakly decreasing scalar-uniformizer norms. It
constructs an actual segment product datum with segment socles, an unlinked
multisegment, all cuspidal ranks one and precisely the target cuspidal content,
together with an actual irreducible-subrepresentation relation into the target
normalized principal series. Repeated target factors and equal norms are allowed.

The proof chooses an unlinked multisegment with the target content. Every base
of a segment occurs in that content, so its rank is one. The sum of cuspidal
ranks gives the required total degree. The canonical segment socles of an
occurrence list realize an actual datum with that same multisegment. The
ordered-content map construction gives a nonzero intertwiner to the target
principal series. The source product is irreducible by unlinkedness, hence the
nonzero intertwiner is injective.

`unlinkedEmbeddingDatum` chooses such an actual datum together with all the
stated witnesses, using classical choice. The construction is uniform in the
field universe and the independent representation-carrier universe.
