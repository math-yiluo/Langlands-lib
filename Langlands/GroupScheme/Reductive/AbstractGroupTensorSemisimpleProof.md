# Tensor products of semisimple representations of abstract groups in characteristic zero

`Langlands.GroupScheme.charZeroAbstractGroupTensorSemisimple` proves the
published `CharZeroAbstractGroupTensorSemisimpleStatement.{u, v, w₁, w₂}`.
For every characteristic-zero field and every abstract group, the Mathlib
tensor product of two semisimple finite-dimensional representations is
semisimple. The field, group and two vector spaces range over four
independent universes.

The proof applies `abstractGroupTensorSemisimple_of_envelopes`. That
reduction chooses finite coordinates for the two representations.
`hasFiniteCoordinateEnvelopes` takes the joint image in the rational
points of the product of general linear groups and uses its vanishing
ideal to form a reduced affine envelope locally of finite type.
The lifted rational family is dense, and the two projection
representations recover the original coordinate actions along that family.
The dense-family comparison transports semisimplicity from the coordinate
actions to the matrix representations of the envelope. The algebraic
tensor theorem gives semisimplicity of their Kronecker product.
The same comparison and the tensor coordinate equivalence carry this back
to the Mathlib tensor product on the original vector spaces.

The algebraic tensor theorem is the second conjunct of
`CharZeroSemisimpleRepresentationIdentityComponentStatement`.
`charZeroSemisimpleRepresentationIdentityComponent_of` supplies it from
`charZeroReductiveSemisimpleRepresentation` and the representation
field-extension result. The latter is obtained by applying
`semisimpleRepresentationFieldExtension_of_algebra` to the Library theorem
`Langlands.Algebra.semisimpleScalarExtension`.

This implements the closure argument of J. S. Milne, *Algebraic Groups*
(2017), Corollaries 22.44 and 22.45, printed p. 478 (PDF p. 494), with
the schematic density convention of corrected Definition 1.48. The
algebraic tensor step uses Theorem 22.42 and Proposition 4.19. The book is
registered as `milne-2017-algebraic-groups`.
