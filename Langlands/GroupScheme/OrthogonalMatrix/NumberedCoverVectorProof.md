# Numbered vector eigenbasis of an aligned split orthogonal cover

This proof establishes the exact published `NumberedCoverVectorStatement` at
all universes and over every field. The supplied pinning, its exact Cartan
numbering, the actual central isogeny and its full scheme-kernel alignment
remain the inputs.

The standard-torus transport is chosen over the original field. The descended
numbered-weight construction uses simple connectedness and kernel alignment to
produce actual pinning-torus characters, their numbered simple-root identities,
and every signed-pair root identity. Its integral normalization supplies a
coordinate permutation and one integer-unit sign for each numbered character.

The standard-torus transport also supplies one base-field basis of rows whose
inverse-right eigencharacters are the negatives of the standard vector
characters, on every commutative coefficient algebra. Reindex this basis by
the stored coordinate permutation and multiply each sign by the negative of
the stored sign. The negative standard character then equals the requested
signed descended character. Pullback along the torus map identifies it with
the signed numbered character of the actual pinning torus. This reindexing
uses the same basis over the original field for all coefficient algebras.

The proof combines the numbered root identities and this basis identity to
inhabit the unchanged Library proposition. All coordinate and coroot
normalization is integral; no field characteristic, finite-field or rank-four
case is excluded. This is an internal composition of the helper constructions,
with no additional classification premise.
