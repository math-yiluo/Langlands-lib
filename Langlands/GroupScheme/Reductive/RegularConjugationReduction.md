# Reducing conjugation maps to finite regular representations

This internal construction works over a field of arbitrary universe `u`, with
small finite coordinate types as in the geometric-reductivity target.

`MatrixLinear.precomp c C` gives the coefficient matrices of a linear
matrix-valued map precomposed with a rectangular linear map `C`. Its evaluation
after every homomorphism of commutative rings is evaluation of the original
linear matrix at the scalar-extended image under `C`. The proof expands the two
finite sums, interchanges them and uses associativity.

For an affine acting group, `ConjugationLinearMap.precomp` combines this
coefficient construction with an actual representation intertwiner. The
published `Intertwines.points` identity holds on every relative test scheme and
changes the argument of the original conjugation-equivariance equation to the
linear image. The resulting map remains conjugation equivariant on all test
schemes. The test schemes have no affineness or reducedness restriction.

`exists_invariant_polynomial_of_scalar` combines the existing determinant
construction with a supplied nonzero scalar identity value. Its degree is
positive because the auxiliary coordinate type is nonempty, and its value is
nonzero because the determinant is the corresponding power of the nonzero
scalar. Its invariant-polynomial predicate is the unchanged all-test predicate.
This result does not require the acting group to be affine.

`exists_conjugation_map_of_affine_regular` is an explicit reduction theorem.
Its hypothesis is the still substantive construction of conjugation maps for
every finite regular subspace whose supplied fixed vector expands to the
constant function one. The finite regular representation and its stability
condition use precisely the coordinate algebra and second-factor translation
convention of `affineRegularRepresentation`. Given this hypothesis, the theorem
constructs a map for any nonzero fixed vector in any finite representation of
the same affine group.

The proof first constructs the normalized finite regular map using
`exists_affine_finite_regular_map_to_one`. Its intertwiner transports fixedness,
and the normalized vector has the required expansion to one. Applying the
explicit regular-subspace hypothesis and precomposing gives the required map
and preserves its nonzero scalar identity value. The initial map into the
regular subspace need not be injective.

The provenance is internal: finite sums, matrix associativity, the existing
all-test intertwiner bridge, the normalized regular-map construction and the
determinant formula give these results. No regular-subspace conjugation map is
constructed here. In particular, the hypothesis of the reduction theorem is
not a proved Steinberg or Haboush input. This module does not inhabit either
`SimplyConnectedPositiveCharConjugationMapStatement` or
`ReductiveGeometricReductivityStatement`, and those exact propositions retain
all of their original proof obligations.
