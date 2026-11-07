# Spherical irreducible embeddings into duals of ordered unramified series

This internal construction gives an actual irreducible admissible spherical
subrepresentation of the smooth dual of the Langlands-ordered unramified
principal series. It allows repeated characters and distinct characters of
equal norm, and is uniform in the field universe. It does not yet construct a
quotient of the original series or prove spherical generation.

Inverting each nonzero complex parameter reverses weak norm order. The
unlinked segment-product embedding for this inverse tuple therefore applies.
`exists_inverse_tuple_segment_dual_embedding` transports that actual irreducible
embedding through `principalSeriesOfTupleSmoothDualEquiv`, retaining the
segment socles, unlinkedness, rank-one conditions and exact inverse-character
cuspidal content.

For each lifted rank-one object, its actual group action is scalar multiplication
by the corresponding unramified character composed with determinant. This is
verified directly from its definition. Worker 706's spherical segment-product
construction applies to this exact content: every base occurs in the total
content, so every segment socle has its full carrier fixed by the
determinant-norm-one subgroup; normalized induction has a nonzero spherical
vector. Transporting the embedding back to the admissible inverse-tuple
principal series proves admissibility of the embedded representation.

`exists_spherical_irreducible_subrepresentation_smoothDual` assembles those
witnesses. `sphericalDualEmbeddingDatum` chooses the resulting actual smooth
representation with its admissibility, actual irreducible embedding and
nonzero spherical fixed-space proofs. Its carrier universe is the field
universe, which is also the carrier universe of the actual principal series.
The construction is an internal composition of the named Library interfaces;
it imposes no additional character regularity or source irreducibility premise.
