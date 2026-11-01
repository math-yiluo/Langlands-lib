# Restricted rank-one extension reverse L-divisibility

Authors: Worker 469 and Worker 46. The dependent-data shape transport adapts
Worker 46's construction.

`Langlands.RankinSelberg.rankOneExtensionLDivisibility.{uF,uV,uW}` proves exactly
`Langlands.RankinSelberg.RankOneExtensionLDivisibilityStatement.{uF,uV,uW}`
from `RankOneExtensionDivisibilityStatement`. It has no additional hypotheses.
For the canonical p-adic data, a supplied self-dual additive Haar measure,
arbitrary quasicharacter and full Whittaker-type representations, including
reducibles, it constructs certified polynomials `Pbase` and `Pind` for the
actual base and upper-induced pairs and proves `Pbase ∣ Pind`.

The test rank is `r+1`, the base factor rank is `t+1`, and the original bound
`t+3 ≤ r+1` is retained. The induced representation is exactly
`F.canonicalNormalizedProductInduced (Shahidi.twoBlocks 1 (t+1) …)
(Shahidi.pairFamily χlift σ₁)`, with ordered blocks `(χlift,σ₁)`.
Only the rank-one complex carrier is lifted to `ULift.{uW} ℂ`.
The field and the two original carrier universes remain independent.

## Actual full type and both certificates

`rankOneExtensionUpper_whittakerType_of_normalizedProduct` specializes the
full normalized-product theorem to predecessor ranks `![0,t]`. Its carrier
family is exactly `Shahidi.pairCarrier (ULift.{uW} ℂ) W`. The proof packs the
positive size function, rank-sum certificate and dependent representation
family into one sigma type. Finite case analysis proves equality with the
exact upper `![1,t+1]` data. Transporting the full Whittaker-type predicate
along this equality identifies the actual representations without exchanging
their blocks or changing their carriers.

This transport adapts Worker 46's dependent-data pattern in
`TwoBlockLConditionalAssembly`; that module is not imported. The mathematical
input is the published closed `normalizedProductWhittakerType` from
`NormalizedProductWhittakerTypeProof`. It supplies admissibility, finite
generation and the entire one-dimensional Whittaker-functional space, with
no irreducibility restriction.

The published `rankOneExtensionCharacter_isOfWhittakerType` supplies full type
for the precise conjugated scalar action used by the target. Its smoothness
is also published in `RankOneExtensionCharacter`. This uses the actual
canonical linear equivalence for the rank-one lift.

`rankOneExtension_certificates_of_inputs` applies polynomial existence to
both actual pairs. The base instance has universes `(uF,uV,uW)`; the induced
carrier requires `(uF,uV,max uF uW)`. Both use exactly the supplied self-dual
Haar measure. The final theorem supplies both instances with the published
closed `symmetricLPolynomialExists` from
`SymmetricLPolynomialExistenceProof`. Its certificates include existence of
compatible quotient measures and one polynomial valid for every such measure.

## Strict span comparison and algebraic extraction

`rankOneExtensionLDivisibility_of_certificates_and_span` first applies the
published `rankOneExtensionSymmetricLPolynomial_iff` to the upper-induced
certificate. This gives the same polynomial for the actual lower model
`rankOneExtensionLowerInduced F t χlift σ₁`. That transport uses the proved
lower-to-upper reversal and tensor equivalences in
`RankOneExtensionFactorTransport`; the lower block order is `(σ₁,χlift)`.
It does not identify the two upper block orders.

The strict rank bound places both certificates in the unequal-rank branch
of `IsPadicSymmetricLPolynomial`. Each supplies a compatible quotient measure,
its right-invariance instance and normalized Laurent generators for every
permitted block. The proof selects `j=1,k=r-t-2` from the base certificate and
`j=0,k=r-t-2` from the lower-induced certificate.

The published closed `rankOneExtensionSpanComparison` from
`RankOneExtensionSpanComparisonProof` supplies inclusion of precisely these
two Laurent spans with the same additive measure and the two independently
compatible quotient measures. Its analytic proof combines
`rankOneExtensionLowerJacquetFunctional` and
`lowerBlockQuotientDisintegration`, implementing the strict compact-section
and Fourier-smoothing comparison. The comparison scalar is finite, nonzero and
independent of the complex variable; integrability and rational continuation
are part of that comparison. This module reuses the closed result.

`normalizedGeneratorSpanDivisibility` from `LaurentDivisibilityProof` converts
the span inclusion into `Pbase ∣ Pind`. Its algebraic proof clears a Laurent
power and removes that power using the normalization `Pbase(0)=1`.
The two quotient measures live on different groups; the assembly neither
identifies them nor changes the supplied additive Haar measure.

`rankOneExtensionLDivisibility_of_inputs` assembles these steps under four
explicit inputs. The final theorem discharges all four with actual published
proofs: full normalized type, common polynomial existence at the base and
induced universes, and the strict span comparison. None remains a premise of
`rankOneExtensionLDivisibility`.

## Provenance and dependency direction

This module is a derived assembly of the named Library results. The source
assertion is Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg
Convolutions* (1983), Lemma 5.5, printed pages 423–427 (one-based PDF pages
58–62). The induction conventions are in Section 3.1, printed pages 404–405
(PDF pages 39–40). Worker 469 previously read these original passages and the
relevant source notes while developing the transport and analytic interfaces.
The source is registered as `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
at `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.

The proof preserves the early Lemma 5.5 route used later in Section 7.
It imports no L-multiplicativity proof, equal-rank extension endpoint or
Section 9.3 representation-theoretic tail comparison. Its full-type
dependency imports `MultiplicativityStatement` for the shape framework and
proposition definitions, not for a multiplicativity theorem. Generic
tail-named measure infrastructure in the analytic closure supplies the
independent block-coordinate and measure results described in the span
proof's companion.
