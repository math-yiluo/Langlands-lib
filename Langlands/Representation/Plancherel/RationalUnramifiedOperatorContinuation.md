# Continuing supplied rational linear operator families

This is a derived construction for Waldspurger IV.1, printed p.277 /
PDF p.43 of `waldspurger-2003-plancherel` (SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`).
There a rational compact operator family has one regular denominator
clearing each fixed-vector image, and the source extends it to the
nonzero locus of that denominator.

The present module constructs this extension as a family of linear maps
on actual unramified character parameters, from a supplied rationality
witness on a region containing a nonempty ambient open subset. It does
not yet prove that these continued linear maps intertwine a
parameter-dependent representation action.

## Global polynomial extensions

For an arbitrary norm-character family and a local vector family `f` on
`Omega`, `PolynomialExtensionData Omega f` records a family of vectors on
the full character space, a finite regular expansion there, and agreement
with `f` on `Omega`. `polynomialExtension` selects the finite expansion in
the existing `IsPolynomialOn` predicate and evaluates the same coefficients
and fixed vectors on all characters. This first construction uses no
geometry, topology on the carrier or finite-dimensionality.

For uniqueness and operator linearity, the character family consists of
all rational norm characters of a connected reductive group scheme `G`
over an arbitrary-universe nonarchimedean local field of arbitrary
characteristic. A topology on its rational points and continuity of
`rationalValuationImageProjection G` are explicit. The original region
contains an open nonempty subset `D` of the full character space.

`polynomialExtensionData_unique` subtracts two global polynomial
extensions. The difference vanishes on `D` by agreement with the original
family. The published vector uniqueness theorem makes it zero everywhere.
The arbitrary region `Omega` itself need not be open.

`polynomialOperatorExtension` extends the image of each fixed input vector
using `polynomialExtension`. For additivity, the sum of the extensions of
two input vectors is a polynomial extension of the original image of
their sum. Uniqueness identifies it with the selected extension of that
image. Scalar multiplication follows in the same way, using the scalar
multiple of the identity linear map to transport the finite expansion.
The result is therefore an actual linear map at every parameter.
Its global polynomiality and agreement with the original operator on
`Omega` are proved separately. Source and target carriers have independent
universes.

## Numerator and regular region

`RationalOperatorContinuationData Omega A` consists of one regular
denominator nonzero on `Omega`, a global polynomial family of linear maps,
and equality of that numerator with `b(chi) * A(chi)` on `Omega`.
Its `regularRegion` is the full nonzero locus of that denominator.
It contains the original region, by the recorded nonvanishing premise.

`continuedOperator` divides the global polynomial numerator by this
denominator only at a character in `regularRegion`. The result is rational
there with the same denominator. The proof cancels the denominator and its
inverse and reuses the global numerator's finite expansion. The agreement
theorem proves restriction to `Omega` recovers each original linear map.

`rationalOperatorContinuation` starts with the supplied
`IsRationalOperatorOn Omega A` witness, selects its original denominator,
and applies `polynomialOperatorExtension` to the cleared operator family.
Thus the continuation is constructed from the supplied operators and
their finite numerator expansions. No independently chosen extension
values are assumed as data.

The final uniqueness theorem compares any two such continuation records
for the same original family. Their regular regions both contain `D`.
Restrict both rational families to the intersection of their regular
regions, where they agree on `D` with the original family. The published
rational operator uniqueness theorem then gives equality at every common
regular value. Selected denominators may have different zero sets; the
result does not assert a maximal region of regularity or define values
at their zeros.

## Source scope and remaining obligations

The source's rational families live on the representation orbit and
intertwine the actual normalized induced actions. This module constructs
only their underlying linear continuation on actual character parameters.
It assumes the original rationality predicate and does not prove
convergence or rationality of the actual standard integrals. Polynomial
dependence of the representation actions and equivariance of the
continued maps, representative transport, descent to the orbit, generic
irreducibility, the opposite-composition scalar `j` and the density `mu`
remain separate obligations. These mathematical premises are not
structural assumptions discharging the main Plancherel program.
