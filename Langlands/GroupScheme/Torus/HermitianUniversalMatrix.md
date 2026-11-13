# The actual Hermitian universal Laurent matrix

This internal bridge removes the Laurent-isometry premise from the conditional
faithful-torus Witt bound. Let `K` and `L` be fields in a common arbitrary
universe, with `L` a `K`-algebra and a finite `K`-basis of the full `N` by `N`
matrix algebra. For any additive commutative monoid `M`,
`map_tensorCoefficients_tensorMatrixEquiv` identifies the actual all-test
matrix coordinates on `Spec K[M]`, transported by `tensorCoefficients`, with
`laurentMatrixEquiv` applied to the actual affine unit coordinates. The proof
first uses the affine global-section comparison, then the tensor swap and
scalar tensor equivalence. This part needs no quadratic-extension assumption.

For a split-torus morphism `i` with finite index type `I`,
`inverseUniversalTensorMatrix i` is the actual tensor-coefficient matrix of the
inverse of the universal point followed by `i`. The theorem
`inverseUniversalMatrix_eq_map_tensor` identifies its transported coefficients
with `inverseUniversalMatrix i`. This follows from the preceding comparison
and preservation of inverses by the affine point equivalence.

Now assume that `L/K` is separable quadratic. If the all-test matrix images of
`i` satisfy the full conjugate-transpose Gram equation for a field matrix `J`,
`inverseUniversalMatrix_preservesGram` gives that equation for the inverse
universal Laurent matrix. A group-scheme morphism commutes with inversion, so
the assumed all-test equation applies to the inverse universal point.
`tensorCoefficients_preservesGram` transports the entire equation, identifying
conjugation with coefficientwise conjugation and field entries with constant
monomials. No rational-point separation or characteristic restriction occurs.

Finally, `card_le_wittIndex_of_allTest_isometry` applies this preservation result
to the previously constructed weight-isotropic subspace bound. For a
monomorphism of the underlying schemes and an actual nonsingular Hermitian
form, the cardinality of `I` is at most the form's attained Witt index. All
pairing arguments retain the full two-vector Gram equation, including in
characteristic two. The all-test preservation premise remains explicit; this
module does not construct a presentation or assert equality with the split
rank of an arbitrary ambient group.

The provenance is internal: the proof composes the actual affine matrix
comparison, scalar tensor equivalence, group-object inversion law, full Gram
transport, and the finite matrix algebra weight bound. No rank-classification
result is used.
