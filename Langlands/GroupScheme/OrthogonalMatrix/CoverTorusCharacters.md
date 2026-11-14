# Character descent through the orthogonal-cover torus comparison

This internal helper uses the comparison data of `StandardTorusTransport`.
Its comparison map has exactly the kernel of the original supplied cover on
every relative test scheme. The proof evaluates the comparison square, using
the monomorphism of the standard torus and the inner automorphism isomorphism.

`exists_character_comp_eq_iff` applies fpqc character descent to that map.
A character descends to standard orthogonal coordinates if and only if it
kills the full original cover kernel. `descendCharacter` chooses the descent,
and `torusMap_comp_descendCharacter` proves its factorization. No reducedness,
smoothness of the kernel, or restriction on the characteristic is used.

The provenance is internal: the kernel comparison and character construction
are direct consequences of the comparison square and the published fpqc
homomorphism descent used by `CoverTorusTransport`.
