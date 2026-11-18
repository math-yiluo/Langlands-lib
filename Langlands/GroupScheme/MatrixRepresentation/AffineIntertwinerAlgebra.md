# The actual intertwiner algebra and the operator commutant

This internal comparison supports Milne, *Algebraic Groups* (2017),
Proposition 4.19(c) and Remark 4.18, pp. 90–91
(`milne-2017-algebraic-groups`). `intertwinerAlgebra` is the matrix algebra
corresponding to the commutant of the affine coefficient-generated operator
algebra.

The all-test intertwiner comparison with universal coefficients shows that this
algebra consists exactly of the actual self-intertwiners. In particular it is
equal to the `Algebra.adjoin` of self-intertwiners used in the unchanged target.
The matrix-to-endomorphism equivalence identifies it, and that exact adjoin
algebra, with the operator commutant.

For a semisimple actual representation, the proved bicommutant theorem identifies
the centre of the operator algebra with the centre of this commutant.
Transporting through the preceding algebra equivalence gives
`operatorCenterEquivEndCenter`. Hence the target's étale-centre hypothesis is
also an étale-centre hypothesis on the operator algebra. The implementation keeps
all-test intertwining, arbitrary affine group schemes, and arbitrary fields.
