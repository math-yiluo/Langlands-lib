# Globalizing local slices of a scheme relation

This helper develops the globalization step of the direct etale-slicing proof.
It does not assert the existence of local slices or use a quotient theorem.

A finite type point here means a point whose canonical residue-field morphism
is locally of finite type. A point closed in an open subscheme has this
property in the ambient scheme: its residue-field morphism into the open
subscheme is a closed immersion, and the residue fields of an open immersion
are isomorphic. Residue-field naturality and invariance under isomorphism give
the assertion.

The open coverage test follows directly from compactness of an affine chart.
If a point lies outside the open subset, choose an affine chart above it. The
closed nonempty complement in that chart contains a closed point, which is a
finite type point of the ambient scheme by the preceding lemma. This contradicts
the assumed containment. These are internal helper results, proved from Mathlib
and motivated by the finite-type-point reduction in the task context.

The final theorem assumes local slices meeting all finite type points, chooses
one slice for each such point, and forms their scheme coproduct. The index is
a subtype of the underlying set of the target scheme, so it lies in the same
universe. Local finiteness of type of the coproduct map follows by source
locality. Pulling the coproduct open cover back to the relation pullback
identifies each chart map with the corresponding local etale map, proving
etaleness by source locality. Every local image lies in the global image by
the canonical pullback map. The global image is open because the map is etale,
and the coverage test makes it all of the target. No smoothness, relation,
or quotient theorem is assumed by this conditional globalization result.
