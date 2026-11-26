# Summable inverse powers of adelic height on rational points

`RationalAdelicHeightSummabilityStatement` concerns a matrix representation of positive
size that is a closed immersion, over a number field. It asserts summability over the rational
points of the group of the reciprocal of a fixed natural power of the full adelic height.
The exponent depends on the field and the representation.

`rationalAdelicHeightSummability` sends a rational matrix to the projective point whose
coordinates are one followed by the matrix entries. The coordinate one makes this map
injective on matrices. A closed matrix representation is injective on the principal rational
points, so the map from rational group points is also injective.

The argument compares heights place by place. At each finite place the matrix-and-inverse
maximum bounds the matrix entries and is at least one. At an infinite place it has the same
two bounds after multiplication by the matrix size. The comparison of the primitive-vector
height with the multiplicative Weil height then gives an upper bound on the projective height
by the full adelic height. Restricting `summable_projectivization_mulHeight_rpow` to the
injective map bounds the wanted series by a convergent series. Its real exponent may be
chosen to be a natural number.

The statement is derived from the projective height summability theorem and the local
inequalities for `AdelicMatrixHeight.height`. It gives the arithmetic summability used to
bound sums over rational cosets by choosing one representative of each coset.
