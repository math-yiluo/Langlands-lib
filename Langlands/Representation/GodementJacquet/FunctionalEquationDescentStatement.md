# Descent through actual matrix coefficient inclusion

`NormalizedMatrixFunctionalEquationDescentStatement` is an internal conditional
statement about two actual complex representations of the same general linear
group. The field and both representation carriers have independent universes.
Every rank `n + 1`, including `n = 0`, is included.

The ambient representation `σ` is assumed to carry the complete unchanged
`NormalizedMatrixFunctionalEquationData q ψ ν abv μ σ P PDual c m`.
The target representation `τ` has its actual bi-smooth coefficient submodule
contained in that of `σ`. The two Laurent spans of target rational values,
ordinary and inverse-transpose, must each contain `1`. Pointwise rationality
alone does not replace either premise. The residue parameter satisfies `1 < q`,
and the supplied additive Haar measure is self-dual for the supplied character.
The topological hypotheses are those of the published full rectangular
Schwartz Fourier equivalence.

The conclusion constructs polynomials `Q`, `QDual`, a complex unit `d` and an
integer `a` giving the complete normalized matrix data on `τ`. These parameters
may differ from the ambient ones. In particular, coefficient inclusion does
not assert equality of the two value modules or preserve their normalized
generators.

The unchanged conclusion retains common convergence half-planes, rational
continuations and both reciprocal-polynomial generator equalities with constant
coefficient one. For every full-matrix test it retains a Fourier witness before
all target coefficients and all actual continuation pairs, with both denominator
guards. The scalar Fourier measure, its square product, the plus transpose
pairing, the inverse-transpose coefficient, the normalized shifts, the variable
`q^(-s)`, central scalar `1` and sign exponent `0` are unchanged.

This statement is derived internally from the Library interfaces rather than
translated from a new literature theorem. Coefficient inclusion permits
restriction of both convergence and continuation assertions and of a common
denominator. The published `normalizedGeneratorExistence` explains why the two
memberships of `1` allow new normalized generators. The ambient normalized
equation supplies a rational gamma identity. The published rectangular Fourier
equivalence supplies both incidences of the target value families, allowing
`gammaNormalization_of_incidence` to produce the new unit and integer exponent.
This describes the intended implication, not a proof supplied by this module.

For an actual smooth subquotient, the published
`subquotientCoefficientInclusion` can discharge the coefficient inclusion.
Producing the two memberships of `1` is a separate obligation. The statement
neither asserts unconditional analytic existence nor completes
`GenericMatrixFunctionalEquationStatement`. Worker 364 designed this helper
with Worker 704's descent route and identification of the existing algebraic APIs.
