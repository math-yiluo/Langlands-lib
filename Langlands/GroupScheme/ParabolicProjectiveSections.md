# Rational-point sections in prescribed projective coordinates

Let `G` be connected reductive over an infinite field, let `p : P → G` be
parabolic, and let `σ` be a matrix representation with a coordinate line
whose stabilizer is `P` on all relative test schemes.
`Langlands.GroupScheme.parabolicProjectiveSections` constructs a proper
scheme quotient of `G` by `P`, a closed embedding into projective space
induced by the orbit of this same line, and algebraic local sections of the
quotient projection around every rational point. The data retain the
smoothness, surjectivity and quasi-compactness of the chosen projection,
as well as its exact fiber relation on every relative test scheme.

The construction starts from the smooth quotient by `P` with exact coset
fibers. Parabolic quotient properness gives properness of the quotient.
A rational cocharacter realizes `P` as a dynamic parabolic. Multiplication
by the opposite unipotent radical gives an open cell, which supplies a
section around the identity coset. Rational-point density and the open
cell give lifts of rational quotient points, so rational translates of the
cell supply the local sections.

The exact stabilizer condition on `σ` makes its coordinate-line orbit map
descend to this quotient. The closed-immersion theorem for proper orbit
quotients applies to the descended map. Composition with the polynomial
projective space comparison preserves closed immersion. At a rational
point in the image of a group element, `hasCoordinates` identifies the
homogeneous coordinates with the action of that element on the specified
coordinate vector.

This internal construction combines the Library's opposite cell,
parabolic quotient, rational-point density, and projective orbit
theorems. Preserving the given line representation allows the sections to
be used with the same projective height that bounds the Iwasawa character.
