# Coefficient bounds on central cocharacter lattices

Internal helpers for the Xi upper-bound proof.

The imported `RationalFaceLattice` module defines `faceCocharacterLattice J`
as the kernel of the integral pairing with the roots
in `J`. Its uniformizer powers lie in the standard Levi and commute with all
of its rational points. The centrality proof evaluates the published equality
between the standard Levi and the centralizer of the cocharacters annihilating
`J`, using an existing standard cocharacter.

Its `jacquet_mk_action_eq_sqrt_smul` rearranges the definition of the normalized
Jacquet action. It multiplies the published inverse-square-root formula by the
positive square root of the modulus; the scalar is nonzero since the modulus
takes values in positive units.

`faceUniformizerPowers_modulus` applies the published central modulus
factorization to identify the modulus of the standard unipotent radical with
the minimal modulus on the face lattice.

`exists_face_jacquet_coefficient_height` assumes uniform unipotence on the
normalized Jacquet action restricted to that lattice. Its degree is chosen
before the vector, Jacquet functional, and translation. For each translation
it bounds the unnormalized quotient coefficient by a nonnegative constant
times the square root of the minimal modulus of the translated point, times a
power of one plus its actual matrix height. The proof applies the unipotent
lattice height bound to the quotient of the translated vector, undoes the
normalization, and divides the constant by the positive half modulus of the
fixed translation.

These are derived helpers using the actual group and Jacquet definitions.
They do not prove Jacquet unipotence or the Xi upper bound.

`rationalFaceJacquetCoefficientBound` packages the coefficient theorem as the
exact proposition `RationalFaceJacquetCoefficientBoundStatement` at arbitrary
universes for the field and the complex vector space.
