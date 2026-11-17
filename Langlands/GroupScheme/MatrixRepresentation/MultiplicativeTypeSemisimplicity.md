# Semisimplicity of actual multiplicative-type representations

This module proves the exact first conjunct of the published
`MultiplicativeTypeRepresentationGaloisOrbitStatement`: the sum of the
nonzero simple stable subspaces of every finite-coordinate representation
of an affine group of multiplicative type over an arbitrary field is the
whole space. The zero representation is included. No orbit classification,
realization, isomorphism classification or endomorphism-field conclusion is
asserted here.

A subspace of a character space is stable on every affine algebra test,
since the character equation turns each coefficient vector into a scalar
multiple of the original vector. Every nonzero vector in a character space
therefore spans a simple stable line. If the character spaces span the
whole representation, these simple lines prove the required semisimplicity
condition.

Semisimplicity descends along any field extension. A stable original
subspace extends to a stable subspace and has an equivariant projection
onto it when the extended representation is semisimple. Choose an
original-field linear functional on the extension field taking one to one
and apply it to the matrix entries of that projection. Functional descent
of intertwiners proves equivariance. The coefficient-extraction property
of extended subspaces proves that its range lies in the original subspace,
and normalization of the functional proves that the map fixes that
subspace. Its stable kernel is therefore a complementary subspace. The
stable-complement characterization gives original semisimplicity.

Finally extend the field to a separable closure. Multiplicative type is
preserved by this algebraic extension, and the Library's diagonalizability
theorem gives an actual diagonalizable isomorphism there. The complete
character decomposition gives semisimplicity over the separable closure;
the preceding descent theorem finishes the argument. This is an internal
derived proof of the semisimplicity portion of Milne's Theorem 12.30,
using actual affine-test stability throughout and retaining finite
non-smooth groups of multiplicative type.

Source context: J. S. Milne, *Algebraic Groups* (2017), Theorem 12.30,
printed pp. 241–242, one-based PDF pp. 257–258. Only its semisimplicity
conclusion is proved here. The implemented proof descends projections by
a coefficient functional rather than reproducing the book's finite-Galois
category equivalence argument. The group is not required to be smooth;
torsion characters are retained by the diagonalizable decomposition.
