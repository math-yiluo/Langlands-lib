# Representations from ordered matrix projectors

A complete ordered family of orthogonal projectors defines an invertible matrix for every family of unit scalars, by scaling each summand by its assigned scalar. Orthogonality makes this a homomorphism from the componentwise group of unit scalars. Multiplying the weighted matrix by one of the projectors extracts its summand. The construction commutes with change of coefficients.

For a chosen character on each summand, `representation` evaluates each character on points of the diagonalizable group and uses the resulting unit scalars. The natural transformation on affine points induces the actual homomorphism into the general linear group through `Corepresented.groupSchemeMap`. Its coordinate map classifies the weighted matrix at the universal point of the group algebra.

If the characters generate the group of exponents, `isClosedSubgroup_representation` proves that this homomorphism is a closed immersion. The image subalgebra contains the universal matrix entries and the inverse entries. Multiplying by the projector for a given character shows that each entry of the projector times the corresponding monomial belongs to the image. The projector entries generate the unit ideal, so the monomial itself belongs to the image. The inverse matrix gives the negative monomials by the same argument. Together these generate all monomials and hence the group algebra.

This is an internal construction for producing actual subgroup families from the ordered projector schemes. A finite free character lattice gives a split torus by the existing diagonalizable comparison.
