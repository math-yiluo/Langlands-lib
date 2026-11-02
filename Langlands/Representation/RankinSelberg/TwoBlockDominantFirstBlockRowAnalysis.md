# Measurable row averages and the original raw-norm majorant

This module supplies derived analysis for the first-block calculation in
Jacquet, Piatetski-Shapiro and Shalika (1983), §4.9, printed pp.416–418, and
§4.10(2), printed p.419. The source decomposes the rectangular variables and
moves their integrals through the first-block calculation. The present module
makes one local interchange precise using the actual quotient and the exact
supplied product Haar measures. It does not yet prove the global Laurent
identity or the lower-kernel convergence assertions.

The field has its canonical p-adic topology, valuation and Borel structures.
Write `a = m 0 + 1`, `b = m 1 + 1`, and `c = j + k + 1`. The rank equation is
`a + b = t + 1`, and both block sizes are positive. The external dimensions
`j,k` are arbitrary, including zero. The section, block representations,
supplied inverse Whittaker functionals and equivariant large test function
are those of the neighboring first-block modules. The scalar Haar measure
`ν` is arbitrary; every rectangle uses its existing finite product measure.
No nonzero-functional hypothesis is used. The field and block-carrier
universes remain independent. Local test inputs are already Whittaker
functions, so no test-representation carrier is required.

`continuous_translated_unequalRankIntegrandAt` proves joint continuity of
the actual smaller JPSS integrand as a function of its unipotent quotient,
rectangle and large right-translation parameter. It assumes continuity of
the two supplied Whittaker functions and accepts an arbitrary complex
parameter `s` and an equality transporting the large rank. The proof removes
that equality, descends continuity through the open quotient map times the
identity, and checks the actual matrix product and determinant weight on
representatives.

`firstBlockUpperRowAverage_stronglyMeasurable` applies this continuity to
the existing row average. For fixed lower-radical matrix `Z` and base element
`g`, it proves joint strong measurability in the actual small quotient `q`
and second-block columns `Y`. Its hypotheses are continuity of the large
test and smoothness of the first block representation. Smoothness makes
every coefficient in the supplied inverse coefficient model continuous,
including the image of a zero functional. The actual row and column joins
are measurable. The identity `firstBlockUpperRowAverage_eq` then expresses
the average as an integral of the actual small quotient integrand, and
measurability follows by parameter integration. This proof makes no
measurability assumption about `Quotient.out`.

`firstBlockUpperColumnNormProfile` is the real-valued function

`q ↦ ∫ Y, ‖firstBlockUpperRowAverage … s q Z Y g‖ dY`.

The theorem `firstBlockUpperColumnNormProfile_measurable` proves that it is
measurable under the same continuity and smoothness hypotheses. The norm is
taken after averaging the first-block external columns; this profile differs
from the original raw norm, which takes the norm before any averaging.

`firstBlockUpperRowAverage_column_control` starts with integrability of the
original rectangle at the actual block-quotient point
`fiberPoint q (lowerRadical Z * g)`, with weight exponent `s - c/2`. It proves
three facts: the row average is integrable in `Y`; its column norm profile
is at most the original real raw-norm profile at that point; and its signed
`Y` integral equals the original rectangle average. The proof uses
`G = firstBlockEmbedding q.out * (lowerRadical Z * g)` only for a pointwise
calculation. The previously proved change `x = X*G` transports the original
rectangle integrability. The measure-preserving actual column join gives
product integrability, permitting Fubini. The bound follows from
`norm_integral_le_integral_norm` and the exact raw-norm Jacobian cancellation.
These three conclusions require no continuity or smoothness assumptions
beyond the explicit original rectangle integrability premise.

`firstBlockUpperRowAverage_product_control` works with any S-finite measure
`μ` on the actual small quotient. It assumes the preceding original
rectangle integrability for almost every `q` and integrability in `q` of
the original real raw-norm profile. Together with the stated large-test
continuity and first-block smoothness, these imply integrability of the
actual `(q,Y)` row-average function for `μ.prod (rectangularMeasure ν j b)`.
Indeed, its measurable column norm profile is dominated almost everywhere
by the given integrable original raw profile, and the separate column
integrability holds almost everywhere. The product integrability criterion
then applies. Only after establishing this convergence does the proof
interchange `q` and `Y`, obtaining the integral of the original rectangle
average as `∫ Y, ∫ q, firstBlockUpperRowAverage …`.

The last theorem exposes local analytic hypotheses for later use with the
existing original-product disintegration and quotient kernels. It does not
assert those hypotheses globally or replace their proofs by total Bochner
identities. No epsilon witness, polynomial identity, or bilateral-series
cancellation enters this module. Its arbitrary complementary dimensions,
explicit measure choices and real norm majorant are derived refinements of
the cited JPSS calculation, rather than separately quoted source statements.
