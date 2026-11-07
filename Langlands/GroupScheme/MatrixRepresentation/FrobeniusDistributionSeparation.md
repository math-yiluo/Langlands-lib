# Separation of actual distributions by finite original representations

This is a derived construction and separation argument for any affine group
scheme `G` over a field `k : Type u`. No finite-type, reducedness, algebraic
closedness, or ordered-coordinate hypothesis is imposed.

## Finite comatrices in the original group

`representationOfComatrix` takes a square matrix `M` in the actual coordinate
algebra `CharacterUnits.Coord G`, indexed by `Fin N`, whose coproduct and counit
are the matrix multiplication and identity formulas. It applies the existing
`AffineLinearEmbedding.toGLHom` to the canonical corepresentation
`TorusActionCoordinates.corepresentation G`, then restricts along the inverse
of its group-scheme comparison with `G`. The result is a finite matrix
representation of the original group.

`universalCharacterMatrix_representationOfComatrix` proves that its universal
matrix is exactly `M`. The proof evaluates at the original universal point,
cancels the affine-model comparison and its inverse, and uses the
corepresentation equivalence and its inverse to recover each entry.

The existing `Lie.exists_representation_coefficient_span` from
[`Lie/ConjugationSemisimple`](../Lie/ConjugationSemisimple.md) supplies the
coefficient-span result: every coordinate belongs to the span of one finite
original representation. Its `representationCoefficients` matrix is
definitionally the same as `universalCharacterMatrix`, and
`AffineCoefficients.coefficientSpace` is that span.
`linearMap_ext_of_coefficientMap` reuses this result directly to prove that
two linear functionals on the actual coordinate algebra agree if their
coefficient matrices agree for every such representation: their difference
vanishes on the spanning entries and hence on each coordinate.

## Actual Frobenius distributions

For an exponential characteristic `p` and any height `r : ℕ`,
`distribution_ext_of_actionAlgHom` proves that the family of original actions
`FrobeniusConvolutionAction.actionAlgHom p r ρ`, over all finite
`ρ : MatrixRepresentation G (Fin N)`, separates elements of the actual
Frobenius-quotient convolution algebra. Pull each distribution back along the
surjective actual quotient map. The quotient-point matrix formula identifies
its coefficient extraction with the stated original action. Coordinate
separation gives equality of the pulled-back linear maps, and surjectivity
gives equality of the distributions themselves.

This proves separation in the actual full convolution dual, rather than only
in the image of a particular action. It supplies no root subgroup existence,
Steinberg module, induced-space support bound, or irreducibility conclusion.
The construction is derived from the imported Library comatrix theorem and
actual-coordinate interfaces; no additional external source is used.
