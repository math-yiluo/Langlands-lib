# Bounded normalizer action on the subgroup coordinate span

This is an internal derived step toward Kaletha–Prasad, Proposition 2.2.16.
It uses the actual split conjugation representation from
`ConjugationSpan.lean`. No local-field, reducedness, density, or faithfulness
assumption is needed once that representation is supplied.

For an affine group scheme over a field with a valuative relation, an
algebraically bounded rational subgroup `H`, a finite matrix representation
`ρ`, and `S : ConjugationSubrepresentation ρ H`,
`S.isAlgebraicallyBounded_normalizer_image` proves algebraic boundedness of the
actual scheme-point image of the full normalizer of `H` under
`S.representation`. `ConjugationBoundedStatement` packages this assertion at
arbitrary field universe, and `conjugationBounded` proves it.

The implemented proof expresses the matrix and inverse-matrix values of `H`
in the split coordinates using `S.retraction`. They span the whole restricted
space because `S.retraction * S.inclusion = 1` and every column of the
inclusion lies in the original subgroup coordinate span. The rational matrix
formula and the projection identity show that the normalizer preserves these
generators. Their coordinate bounds follow from algebraic boundedness of `H`,
inverse closure of `H`, and closure of bounded evaluation families under finite
linear combinations.

The family theorem in `BoundedSpanningAction.lean` therefore bounds the entries
of all restricted normalizer matrices uniformly. The normalizer is closed under
inversion, so the existing
`isAlgebraicallyBounded_image_of_entries` transports these bounds to the
all-regular-functions boundedness predicate on the actual general linear
group scheme. This argument includes dimension zero and requires no separate
compactness or spectral-integrality assertion.
