# Polynomial growth of actual regular functions

This internal, derived unit supplies a quantitative version of the published
coordinate argument in `Rational/MatrixEntryBoundedness`. It works with the
actual global regular functions, actual rational-point algebra evaluations and
the existing residue-normalized rational matrix norm. The affine group scheme
need not be reductive, connected or split, and the field can have arbitrary
characteristic. The finite matrix index type is required to be nonempty, as in
the definition of the matrix norm.

`RegularFunctionPolynomialGrowth F ρ a` is the property that the
residue-normalized absolute value of the evaluation of `a` is at most
`c * rationalMatrixNorm F ρ g ^ d` at every actual rational point `g`, for
one natural degree `d` and one strictly positive real constant `c`. Both
are chosen before `g`. The property is defined for any supplied matrix
representation; the theorem below proves it when the representation is
a closed embedding.

`polynomial_evaluation_powerBound` proves that a polynomial in coordinates
whose norms are bounded by a height at least one has norm at most `c H^d`.
The natural degree and strictly positive real constant are chosen before all
evaluation points. Polynomial induction handles constants, sums and
multiplication by a variable. For sums it takes the maximum degree and the sum
of constants; multiplication by a variable increases the degree by one.
`algebra_evaluation_powerBound_of_polynomial_surjective` lifts this conclusion
through a supplied surjective polynomial presentation. These two lemmas use
an arbitrary normed field and independent universes for the algebra and the
index of evaluation points.

`regularFunction_rationalMatrixNorm_powerBound` instantiates this argument for
a supplied closed matrix embedding of an affine group scheme over an arbitrary
nonarchimedean local field. The closed immersion makes pullback on global
sections surjective. Composing this pullback with the global-section isomorphism
of the explicit general linear spectrum and the two-matrix polynomial quotient
gives a surjective polynomial presentation of the source. Evaluation of each
variable is the corresponding entry of the rational matrix or of its inverse,
so the existing matrix norm bounds every coordinate. The normed-field structure
used in this algebraic estimate is that of the residue-normalized absolute
value; no replacement of the supplied field topology is asserted or needed.

The result strengthens setwise algebraic boundedness to an explicit polynomial
bound, as required by the regular-function estimates underlying Waldspurger's
II.2 and II.3.4. It does not construct the actual parabolic tau-function or prove
modulus-height comparison, unipotent integration, or the conditional standard
intertwining theorem. Its provenance is the explicit polynomial and coordinate
argument above, rather than a claim that those remaining analytic assertions
have been proved.
