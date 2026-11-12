# Affine coordinates for the inverse-right-regular representation

Author: Worker 118.

This internal helper module identifies the actual affine matrix of
`FiniteAlgebraUnits.rightRegularRepresentation b` with the original
`rightRegularUnits b R` applied to the affine unit coordinates.

The proof uses the all-test point formula from `FiniteAlgebraRightRegular`.
The published `Corepresented.pointsEquiv_eq_affinePointsEquiv` and the
corresponding `GL_n` comparison express the two sides after the same
global-section isomorphism. Coefficient naturality and injectivity of that
isomorphism then identify the original matrices over `R`.

`rightMulMatrix_mulVec_repr` is the finite-basis coordinate formula for
right multiplication. Combining these results proves
`affineMatrix_rightRegular_mulVec_repr`: the affine representation sends
the coordinate vector of an element `y` of `R ⊗[k] A` to that of
`y*g⁻¹`, where `g` is the actual affine unit point.

All results hold for a possibly noncommutative algebra with a supplied
finite field basis, over every commutative coefficient algebra, with no
characteristic restriction. No split-torus or group-structure assertion
beyond the given unit-group representation is assumed.
