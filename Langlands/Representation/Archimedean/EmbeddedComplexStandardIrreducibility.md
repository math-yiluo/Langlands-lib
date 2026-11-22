# Complex standard modules embedded in an isotypic module

This argument uses the Library's scalar vector of a complex standard
module and the description of an isotypic module as a direct sum of
copies of a simple type. The scalar vector is supplied by
`ComplexStandardScalarVector.exists_isScalarVector` through the
multiplicity-one calculation for a lowest compact type. See the paired
Markdown of that theorem for its source correspondence.

Write the compact and Lie actions as a free-monoid representation. The
embedding pulls back isotypy from its target. Represent the resulting
isotypic module by finitely supported functions with values in the simple
type. Pick a nonzero coordinate of the given scalar vector in that
description. For each other coordinate, projection to the chosen
coordinate followed by inclusion at the other one would take the vector
out of its scalar line. This linear endomorphism over the monoid algebra
intertwines the compact action, so the scalar-vector property excludes any
other coordinate. Evaluation at the unique coordinate now identifies the
standard module with the simple type.

To compare two lists, sort each one by the real parts of its exponents.
The permutation theorem for irreducible complex standard modules
transfers the isomorphism to the sorted standard module. Both sorted
modules therefore map nonzero to the same irreducible admissible
target. The uniqueness theorem `complexLanglandsQuotientUnique`
identifies their lists up to permutation. Composing with the two
sorting permutations gives the claim for the original lists.
This uses Knapp (1994), (4.3) and Theorem 4(a), (c), p. 405
(one-based PDF p. 415).
