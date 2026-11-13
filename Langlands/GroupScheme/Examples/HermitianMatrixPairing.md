# Gram pairing and actual Witt index

This is internal elementary linear algebra for `HermitianMatrix.Form`.
The column-vector pairing is `sum i j, bar (x i) * gram i j * y j`,
conjugate-linear in the first variable and linear in the second. `sesquilinear`
bundles precisely this pairing. `linearFirst` is its flip, so its value on
`(x,y)` is the original pairing on `(y,x)`. Its type and proved conjugate symmetry
match the inputs of `HermitianRoot.exists_anisotropic_diagonal_coordinates`
when restricted to an anisotropic field subspace. No anisotropy is asserted here.
The additive and scalar laws, Hermitian symmetry and coefficient compatibility
are proved by expanding finite sums and the Hermitian Gram equation.

Total isotropy means that the full pairing vanishes on every pair of vectors
in an actual submodule. In particular it is not merely vanishing of the
self-pairing, a distinction retained in characteristic two. The equivalent
linear-first formulation is proved by swapping the two vectors.

Over a field, `wittIndex` is bounded search for the greatest dimension realized
by such a totally isotropic submodule. The zero submodule supplies a witness,
and every submodule's dimension is bounded by the cardinality of the finite
index type. These two facts prove attainment, the ambient dimension bound,
and maximality. The final characterization records attainment and maximality
without mentioning bounded search. No Witt decomposition or classification
is stored in the form or the Witt index.
