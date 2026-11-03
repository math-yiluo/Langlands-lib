# Galois traces and the largest split subtorus

This is a derived construction from the published actual lattice pairing, Galois
transport, cocharacter averaging and descent, and largest-split-subtorus APIs.
It is an intermediate ingredient for the split-part argument; no reductive-group
centralizer theorem is asserted here.

For an affine torus locally of finite type over a field, cocharacter detection
makes the integral pairing injective in its character argument. The construction
`CharacterAveraging.galoisOrbitSum` sums every Galois translate of an actual
character over a finite Galois extension, without division. The sum is invariant.
Its pairing with any cocharacter equals the pairing of the original character
with the cocharacter orbit sum, by invariant pairing and reindexing by inversion.

Let `i : A → T` be the actual largest split subtorus. If a character of `T_K`
restricts to zero along the base change of `i`, it annihilates the base change
of every cocharacter over the original field: the universal property of `i`
factors each such map from the multiplicative group. Cocharacter orbit sums
have actual descents by the published `descendedOrbitSum` construction. The
pairing identity and factorization therefore show that the character trace
annihilates every cocharacter of `T_K`. Pairing injectivity over `K` forces
that trace to be the zero character.

The extension is finite Galois and the torus is affine and locally of finite
type; no splitting of `T_K`, perfectness of the original field, or rational-point
density assumption is used. Equality to zero is equality of actual character
morphisms, hence includes all test schemes. This module does not construct a
geometric root datum, prove unipotent-weight positivity, or identify the
centralizer of the split part in an ambient reductive group.
