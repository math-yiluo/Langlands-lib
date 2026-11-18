# Actual unramified cancellation in a supplied integral basis

The primary construction is
`Langlands.Plancherel.rationalUnramifiedBasisLaurentEquiv`.
It identifies the existing actual unramified regular-function algebra with
finite Laurent polynomials using any supplied finite integral basis of the
actual discrete valuation image. It composes the basis's additive equivalence
with the published actual valuation-image coordinate algebra equivalence.
No alternate parameter space or regularity predicate is introduced.

`rationalImageBasisUnitaryCharacter` constructs the circle-valued character
with the supplied basis values. `rationalUnitaryParameterOfBasis` uses the
published actual unitary-character equivalence to obtain an actual parameter.
Its surjectivity follows from the basis reconstruction identity for linear
maps, so these parameters cover the entire actual unitary group.
The evaluation theorem proves that the regular-algebra equivalence evaluates
by the same Laurent polynomial on these parameters. Its monomial case uses
surjectivity of the actual valuation-image projection and the finite basis
expansion; addition gives the general case.

`rationalUnramifiedBasisCoordinateRoot` is the image of the first-coordinate
factor `X₀-a` in this actual regular algebra. Its evaluation is `t-a` when the
first circle coordinate is `t`, and the factor is nonzero when `a` is on the
unit circle.
`rationalUnramifiedBasisCoordinateRoot_pow_dvd_of_dense_unitary_bound` says
that, if a power of this factor divides a denominator and a scalar numerator
is bounded by a constant times that denominator on a dense set of actual
unitary parameters, the same power divides the numerator. The proof first
extends the continuous cleared inequality to the entire actual unitary group.
It evaluates the inequality on the reconstructed basis parameters, applies
the Laurent coordinate-power theorem, and transports divisibility through
the algebra equivalence. No ambient-open continuous extension is assumed.

These are internal algebraic consequences used in the cancellation route of
Waldspurger (2003), Corollary V.2.3 and Lemma V.3.1, printed pp.294–295 /
PDF pp.60–61, registered as `waldspurger-2003-plancherel`. They do not assert
that any standard intertwiner has the required bound or pole support.
The integral basis is supplied; choosing a basis whose first vector is a
primitive actual root direction, and proving that the actual operator's
denominator has such root factors, remain separate obligations. The
construction preserves arbitrary field characteristic and works in rank zero
for the coordinate algebra; the coordinate-root result has a nonempty basis.
