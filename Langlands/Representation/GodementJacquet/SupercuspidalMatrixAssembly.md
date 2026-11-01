# Supercuspidal matrix analytic data from the raw monomial equation

This internal assembly separates the raw matrix Fourier equation from the
analytic assertions that follow from it for an actual irreducible supercuspidal
representation. The raw equation remains a premise; this module does not
establish the closed supercuspidal functional-equation statement.

`HasMatrixMonomialFunctionalEquation` is precisely the Fourier and functional
equation part of the existing normalized data with both polynomials equal to
one. A Fourier witness for each full-matrix Schwartz test is chosen before any
coefficient. The equation applies to every actual original and
inverse-transpose rational continuation, with both reduced-denominator guards.
It uses the plus transpose pairing and the product of the supplied scalar
measure, with no measure rescaling. The central scalar is one and the sign
exponent is zero.

For a rationality datum carrying the actual original and dual central
geometric clearings, every original rational value is Laurent. The proof first
uses rational-continuation uniqueness to transfer the original clearing to the
specified rational value. It takes the Fourier witness and an actual dual
continuation, then applies the concrete matrix denominator-cancellation
theorem to the supplied raw equation.

For every dual test, scalar self-duality supplies the existing full square
Schwartz Fourier equivalence. Its inverse produces an original test whose
Fourier transform is the given dual test. Pointwise equality with the raw
Fourier integral identifies the witness supplied by the raw equation. The
original value is already Laurent. Reflecting its Laurent monomial product
and using involutivity of reciprocal rational substitution shows that the
specified dual continuation is also Laurent. Thus the argument covers every
dual test, not only a previously selected Fourier image.

Actual supercuspidality and irreducibility supply the common half-planes and
all rational continuations through `exists_supercuspidalMatrixRationalityData`.
The existing compact-open unit-value construction supplies one in each actual
rational-value family. Since every generating value is Laurent and one belongs
to each family, `isNormalizedGenerator_iff` gives the two normalized polynomial
generators exactly one. The final theorem combines these analytic assertions
with the unchanged supplied raw equation.

The provenance is internal: the proof is an assembly of actual published
convergence, rational uniqueness, Fourier equivalence, Laurent cancellation
and matrix unit-value constructions. No new source interpretation or
representation-theoretic existence premise is hidden in the assembly.
