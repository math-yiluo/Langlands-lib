# Finite polynomial models for intersections of affine test points

Author: Worker 790.

`exists_affine_test_intersection` constructs a finite polynomial test
algebra representing the fibre product of any two finite polynomial test
points of a separated algebraic space over the ground field. No étaleness
of the points or local finite type hypothesis on the algebraic space is
required.

The proof first uses representability of maps from schemes to algebraic
spaces to obtain the represented fibre product. The published closed
diagonal lemmas make it affine and identify its map into the product of
the two test schemes as a closed immersion. The two test algebras are
finite type by their specified polynomial surjections; local finite type
of their product and of the closed subscheme follows. The coordinate
ring therefore has a finite polynomial presentation. Its canonical
spectrum isomorphism and the scheme/algebra-map equivalence transport
the represented square to the required square of affine test points.

`exists_affine_test_pullback` makes the same construction for two maps
between affine tests. It uses the actual relative scheme pullback,
which is affine. A morphism from a scheme locally of finite type over
the ground field is locally of finite type over any intermediate scheme;
base change and composition therefore make the pullback locally of
finite type. Its coordinate ring and canonical spectrum isomorphism give
the required finite polynomial model.

## Provenance: internal

This is a derived algebraic preparation for the analytification
fibre-product proof. It uses the published representability,
closed-diagonal, affine-coordinate and finite-type APIs; it assumes no
unproved analytic preservation or descent theorem. The finite polynomial
presentation used here means finite generation, as in the Library's
`FinitePolynomialPresentation` definition.
