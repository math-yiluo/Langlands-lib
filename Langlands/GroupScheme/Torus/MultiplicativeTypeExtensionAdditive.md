# Additive Hom vanishing for multiplicative-type extensions

Internal reductions toward `MultiplicativeTypeFieldExtensionStatement`.

A multiplicative-type group is diagonalizable after some field extension. Base
change of the one-dimensional vector group is canonically the vector group
over the new field. The imported diagonalizable averaging lemma makes every
base-changed map zero; faithful pullback for the faithfully flat field extension
reflects that equality. The construction `IsMultiplicativeType.additiveHomUnique`
records the actual zero homomorphism as the unique element of this Hom set.

For a represented fppf extension with multiplicative-type outer groups, the
first helper module gives an affine quotient projection and an affine finite-type
middle group. Its quotient-Hom descent then makes every map from the middle
group to the additive group zero. These conclusions do not assume commutativity
of the middle group or connectedness of the quotient. They do not yet establish
that the middle group is of multiplicative type.

This is an internal combination of the published multiplicative-type splitting
predicate and geometry, canonical vector-group base change, faithful flat
pullback, and the quotient and averaging helper constructions. No splitting-field
separability or group smoothness hypothesis is introduced.
