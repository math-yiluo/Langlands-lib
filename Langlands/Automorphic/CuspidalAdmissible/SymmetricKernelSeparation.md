# Orthogonality detected on a polynomial kernel

A locally finite symmetric linear operator preserves a given subspace.
Suppose a vector in a polynomial kernel is orthogonal to the intersection
of that subspace with the kernel. For any test vector in the subspace,
take its finite-dimensional cyclic span for the operator. The span lies
in the subspace and is invariant. Symmetry makes the orthogonal
projection onto the span commute with the operator and with its
polynomials. The projection of the original vector therefore lies in
the intersection in question. Its pairing with the original vector is
zero, so its square norm is zero. This forces the original vector to be
orthogonal to the test vector.

For a smooth group action preserving the inner product, consider two
commuting symmetric operators that commute with the group action.
`fixedPolynomialKernels` imposes fixedness under an open subgroup and
two polynomial kernel conditions. Assume that each vector is fixed by some
compact open subgroup and that each operator is locally finite, so each
vector has a nonzero annihilating polynomial for each operator. Assume
that the joint space is finite-dimensional at each open level for each
pair of nonzero polynomials.

Let the given subspace be stable under the group and both operators.
Intersect it with a joint space containing the vector under consideration
and subtract the orthogonal projection onto this intersection. The
remainder belongs to the joint space. Applying the kernel test twice
removes the polynomial conditions from the orthogonality test. Averaging
over the chosen compact open subgroup removes the fixedness condition,
since it preserves the pairing against a fixed vector. The given subspace
and its orthogonal complement thus form an algebraic direct sum equal to
the whole carrier.

The result uses the Library's finite polynomial cyclic span and
orthogonal projection onto finite-dimensional subspaces. It is an
internal step in the algebraic decomposition of cuspidal forms.
