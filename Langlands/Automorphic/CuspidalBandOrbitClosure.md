# Actual Hilbert orbit containment from smooth scalar coefficients

This internal reduction retains the unproved
`CuspidalHilbertOrbitCoefficientStatement` as an explicit premise. It applies
to every number field in an arbitrary universe with the usual compact
`AdeleQuotient` convention, every actual cuspidal operator realization of
`GL_(r+1)` and its unitary central character.

`sourceBandClosure` is the topological closure of the actual original linear
image in the full canonical determinant-band `Lp ℂ 2` space. The original
image is represented by `translatedToL2` at the identity. It is a Hilbert
norm closure on the noncompact quotient, rather than a derivative compact-open
function closure.

`CuspidalBandOrbitClosureStatement` says that every actual archimedean
translate of each original vector, interpreted as its band `Lp` vector, lies
in this same source closure.
`cuspidalBandOrbitClosure_of_coefficients` proves this conclusion from the
named scalar-coefficient premise.
`CuspidalBandOrbitClosureReductionStatement` states exactly that implication,
and `cuspidalBandOrbitClosureReduction` proves it.

The proof first fixes an arbitrary band `L²` vector whose inner product with
every original source vector is zero. The retained premise supplies the
actual smooth scalar coefficient map, exact enveloping covariance and
genuine joint finiteness. At each standard compact element, the coefficient
of every enveloping derivative is the original functional applied to an
actual compact translate of that derivative, hence is zero.

Published joint-finite analyticity makes each scalar coefficient real
analytic at every actual unit. The published enveloping zero-jet theorem
turns the derivative identities into a zero matrix jet. Published analytic
component uniqueness then gives zero on that compact element's component,
and published compact component coverage reaches every archimedean element.
The argument retains the full compact subgroup, including the disconnected
real components.

The actual translated `Lp` pairing agrees with this zero coefficient.
Hilbert orthogonal-complement separation therefore places the translated
vector in the actual original-image closure. The module proves this
separation step generically for the closure of any linear image in a
complete complex inner-product space.

The provenance is internal composition of the four published analytic
theorems, actual compact translation on quotient functions, translated-band
integrability and Hilbert orthogonal separation. The coefficient regularity,
covariance and joint-finiteness statement is retained as one open premise;
it is not inferred from compact-open orbit density.

The conclusion concerns translates of original algebraic vectors in the full
band space. No group action on every vector of the source completion is
constructed here. Extension to such an action, its smooth-vector
identification, continuous Whittaker uniqueness and unconditional cuspidal
operator multiplicity one remain separate obligations.
