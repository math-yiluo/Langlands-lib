# Normal coordinates for the real spectral stratum

The stratum coordinates split the matrix space into the orbit tangent, polynomial semisimple directions, and a chosen normal complement. The normal projection has kernel equal to the sum of the first two spaces. Its quotient map is a linear equivalence to the normal complement, with inverse induced by the inclusion of that complement.

For an ambient linear map preserving the orbit tangent and fixing the semisimple directions, the absolute normal determinant is the absolute ambient determinant divided by the absolute orbit tangent determinant when the latter is nonzero. The Lean proof uses the more general identity that the ambient determinant is the product of the orbit tangent and normal determinants. In split coordinates this follows from the upper block triangular determinant formula and the identity action on the semisimple factor. In particular, unit absolute determinants on both the ambient and tangent spaces give a unit absolute determinant on the normal space.

Restriction of the trace form to the normal complement identifies the trace conormal with the continuous dual of the normal space. For a trace isometry, precomposition by the normal action corresponds to the inverse ambient action on the trace representative. The functionals annihilate the kernel of the normal projection, and trace isometry then moves the action from the normal input to the trace representative.

These internal identities are used in the real distribution transpose argument.
