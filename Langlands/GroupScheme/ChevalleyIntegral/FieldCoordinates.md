# Coordinate tori and actual root data of field Chevalley groups

This internal comparison expresses the published field Chevalley construction using the coordinate split torus required by the integral-existence target.

For a finite coordinate type `I`, `coordinateTorusIso k I` is the actual isomorphism from the diagonalizable group of the lattice `I → ℤ` to the coordinate split torus over a field `k`. It uses the identity coordinate equivalence in the Library's `Diagonalizable.splitIso`. The character formula `charOf_eq_coordinate` is proved on every test scheme: a coordinate vector expands as the sum of its single-coordinate vectors, so evaluating a character gives the product of the corresponding unit powers. `coordinateTorusIso_character` follows by composing with the inverse torus isomorphism.

For a full root datum `P` on the two coordinate lattices with standard integer dot-product pairing, `fieldRealization_toLinearMap` identifies the transported pairing with the actual character–cocharacter pairing of the coordinate torus.

For any field Chevalley group constructed from integral Chevalley data for `P`, `coordinateTorusHom` precomposes its diagonalizable torus inclusion with the inverse coordinate isomorphism. The maximality lemma uses transport through this torus isomorphism. The actual-root-datum lemma applies `IsRootDatumOf.precomp_torusIso` to the full equivalence between the coordinate field realization and the published Chevalley datum. The character formula verifies that its weight map is the map induced by the actual torus isomorphism. This transports roots and normalizer reflections as well as the entire lattice pairing.

The provenance is internal: this file compares the existing diagonalizable splitting isomorphism, exponent characters, full root-datum realization, and field Chevalley assembly. It supplies field-coordinate compatibility only; it constructs no integral group scheme and proves no assertion about a single group over the integers.
