# The open locus of pointed abelian-scheme structures

`Langlands.AbelianScheme.pointedProjectiveAbelianLocus.{u}` proves
`PointedProjectiveAbelianLocusStatement.{u}`. It constructs an open in the
base of the pointed flat projective family. A test map lands in this open
exactly when the pulled-back family admits an abelian-scheme structure of
relative dimension `g` whose identity is the pulled-back section.

Over a noetherian affine base, `pointedAbelianLawRepresentability` supplies
a locally finitely presented monomorphism representing the pointed laws
for a smooth projective family of relative dimension `g` with geometrically
connected fibres. In an Artinian lifting square, the map from the quotient
test gives a pointed law on the corresponding pullback.
`pointedAbelianArtinianLifting` extends it to the smooth proper family on
the larger test and preserves the prescribed identity section. The
relative dimension remains `g` by base change of the smooth relative
dimension and transport along the isomorphism of families. Classification
gives a map over the larger test, and the monomorphism makes its restriction
equal to the given map. The Artinian smoothness criterion and the open
immersion theorem for flat, locally finitely presented monomorphisms
identify the representing scheme with an open subscheme.

Take the union of the opens over which the family is already pointed abelian
of relative dimension `g`. A map whose image lies in this union admits the
structure by pulling the opens back and gluing. Conversely, a test abelian
scheme restricts to such a scheme at each residue point of the test base.
The geometry lemmas find a noetherian affine open neighbourhood of its
image where the family is smooth of dimension `g` with geometrically
connected fibres. The projective embedding becomes an H-projective
embedding there. The open immersion from the affine argument contains the
point and has a pointed abelian scheme, so its image belongs to the union.

This is the local representability and Artinian lifting argument of
Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, 3rd ed. (1994),
§6.3, Propositions 6.15 and 6.16. The registered source is
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
SHA-256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`,
printed pp. 124–127 (PDF pp. 137–140).
