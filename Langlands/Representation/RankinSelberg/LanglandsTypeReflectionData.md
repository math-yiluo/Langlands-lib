# Reflected residuals for genuine Langlands data

Author: Worker 111.

This internal construction retains certified polynomial data for two original
positive-rank tempered Langlands data and for their reversed inverse-transpose
data. The latter uses the inverse additive character and the same Haar measure,
with its existing self-duality certificate. Independent field and carrier
universes are preserved.

The actual standard-module equivalences transport the dual induced certificate
to the inverse-transpose pullbacks of the original standard modules. The actual
twisted-block isomorphisms transport every dual block certificate to the
corresponding pulled-back original block, using the published arbitrary-rank
transport `IsPadicRankLPolynomial.congr_equiv` of
[segment-pair pole orders](SegmentPairPoleOrder.md). Reversing both finite indices leaves
the full double product unchanged. Positivity writes every block size as a
successor, allowing the closed two-family reflected gamma-ratio theorem to
apply to the original actions.

Each certificate has constant term one. In particular the original induced
polynomial, dual induced polynomial and dual block product are nonzero.
Cancelling these factors from the reflected ratio gives the reciprocal
reflection identity between the two normalized residual polynomials, with an
explicit nonzero coefficient and integral Laurent exponent. This construction
does not assert that either residual equals one or that the parent product
formula holds.

Its provenance is composition of
[certified standard-module data](LanglandsTypeLPolynomialData.md),
[actual inverse-transpose data and equivalences](../Classification/LanglandsInverseTransposeDatum.md),
the closed [gamma assembly](TemperedLFactorGamma.md), and
[residual cancellation](TemperedLFactorAlgebra.md). No new external result is
postulated.

Integration uses module-specific names for local instances. Their types, values,
and local instance scopes are unchanged.
