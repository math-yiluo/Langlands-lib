# Actual prefix-conjugated additive factors of the Steinberg product

This internal construction uses the supplied normalized root maps and reflection
representatives of an actual split pinning over an arbitrary field. It does not
assert their existence. All constructions retain the supplied ordering.

`NormalizedRootParametrization.conjugateHom` postcomposes a supplied additive map
with the inner group-scheme automorphism of an actual normalizer point. It is a
closed subgroup embedding because the original map is closed and the inner map
is an isomorphism. Its scalar evaluation is the actual conjugated point on every
scheme test.

The conjugated map has character `weylAction p.inclusion n a`. To prove its
equivariance, restrict the test torus point by the inverse torus automorphism
through which `n` normalizes the torus, apply the original map's equivariance,
and conjugate back. The character is precomposed with that inverse, in agreement
with the Library's contravariant character convention. This proof uses all
scheme tests and global functions, without restrictions on the field.

`prefixNormalizer` forms each ordered initial product of the supplied reflection
representatives in the actual normalizer. `prefixRootHom` conjugates the map at
position `j` by the product of its preceding representatives; `prefixWeight`
is its integral character. Naturality of ordered prefixes under the Weyl action
identifies this weight with the simple root transformed by the preceding simple
reflections. `prefixSimpleRoots_linearIndependent` then proves that the weights
are linearly independent over the integers. Each map is closed and satisfies the
stated equivariance on every test.
