# Fixed vectors for arbitrary subgroups of coefficient automorphisms

Worker 537. Internal algebraic prerequisite for the stabilizer-fixed character
line in Task 7149.

Let `H` be any subgroup of the automorphism group of a field extension `K/k`.
A `K`-subspace of finitely supported coordinate vectors is invariant if applying
each element of `H` to all coordinates preserves the subspace.
`fixedVectorSpan H W` is the `K`-span of the `H`-fixed vectors in `W`.
`eq_fixedVectorSpan` proves that this span equals `W` whenever `W` is invariant.
No finite-degree, Galois, closed-subgroup, or finite-subgroup hypothesis is used.

The proof generalizes the published minimal-support argument in
`GaloisSubmoduleDescent`. In any nonzero invariant subspace, choose a nonzero
vector with smallest support and divide by a nonzero coordinate. That coordinate
is now one. The difference between a conjugate of the vector and itself has
smaller support, so it is zero. Repeating this step by induction on support
expresses every vector as a sum of scalar multiples of fixed vectors.
`exists_fixed_pi` transfers the normalized fixed-vector conclusion to a finite
function space through `Finsupp.linearEquivFunOnFinite`.

This is an internal generalization of the existing coefficient proof, rather
than an invocation of a finite or infinite Galois correspondence for `H`. Its
role in the representation classification is to produce a vector in a character
space fixed by the character's stabilizer. The module makes no claim about
group-scheme character spaces or the orbit classification itself.
