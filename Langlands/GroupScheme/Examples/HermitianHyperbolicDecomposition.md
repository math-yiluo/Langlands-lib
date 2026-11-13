# Several hyperbolic planes from an actual isotropic subspace

This internal elementary linear algebra construction extends
`HermitianIsotropicDimension`. `HyperbolicDecomposition h r` retains
actual extension-field linear coordinates with `r` hyperbolic planes and
a remaining finite coordinate space. Its full pairing equation has the
linear-first convention, with conjugation on the second vector.
The remaining pairing is a function; no anisotropy is assumed.

The zero construction chooses ordinary coordinates on the entire vector
space. `consCoordinates` reorders a new pair of endpoint coordinates
into the heads of the two families. `cons` combines this reordering with
the existing hyperbolic splitting and a decomposition of its actual
orthogonal middle. The full pairing equation follows by separating the
first terms of the two finite sums. `finrank_eq` follows from the actual
linear equivalence.

`nonempty_hyperbolicDecomposition_of_totallyIsotropic` constructs as many
planes as the finite dimension of any supplied totally isotropic
submodule of a nondegenerate Hermitian space. It inducts on that
dimension. For a nonzero submodule it selects a nonzero vector,
uses `exists_hyperbolic_partner` to split a plane, and applies induction
to the actual isotropic intersection in the middle. The imported
nondegeneracy and dimension lemmas supply the recursive hypotheses.
The trace-one construction of the hyperbolic partner works in every
characteristic, including two.

The fields share an arbitrary universe and the vector space may have an
independent universe. The extension is separable quadratic. This is
internal derived infrastructure for constructing split tori from actual
isotropic subspaces; no outer-form classification or split-rank formula
is an input.
