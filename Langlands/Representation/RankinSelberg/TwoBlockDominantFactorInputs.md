# Factor existence in the dominant-rank assembly

Author: Worker 484.

This internal module records the part of the parent proof that follows
from already published full-type preservation and general pair analytic results.
It supplies no multiplicative comparison and proves neither dominant-rank target.

`upperGammaFactorsExist` first applies
`Langlands.RankinSelberg.normalizedProductWhittakerType` to the given two full
Whittaker-type blocks. This derives full type for the actual canonical normalized
upper induction, including admissibility, finite generation and the complete
one-dimensional functional space. The test carrier and the dependent block
carriers retain their separate universes.

The theorem then applies
`Langlands.RankinSelberg.whittakerTypeGammaConstructionInput` to the test
representation and that actual induction, and separately to each block pair.
`padicSymmetricGammaFactorOfWhittakerType` constructs each certified rational
gamma factor. The input theorem discharges both original and dual analytic
inputs, self-duality and epsilon existence using the published Section 2 pair
theorems. Its paired proof explains their measure and functional uniformity.
The resulting certificates retain those complete quantifiers; the construction
does not merely select rational functions.

`upperLPolynomialsExist` uses the same derived full type and applies
`Langlands.RankinSelberg.symmetricLPolynomialExists` to the induced pair and
each block pair. Choice collects the two block polynomials into one dependent
family. Every resulting certificate has the supplied self-dual Haar measure and
its full compatible-quotient-measure scope.

`lowerReversedGammaFactorsExist` and `lowerReversedLPolynomialsExist` transport
the induced-pair certificates back through `lowerReversedToUpperEquiv`. They
reindex the block certificates by `Fin.rev` at the same time. Thus individual
certificates are also available for the actual lower representation with its
reversed sizes, carriers and representations. The actual normalized equivalence
is essential here; no equality of representations is inferred from commutativity
of factor products.

`gammaConclusion_of_lowerComparison` reduces the upper gamma conclusion to
equality of any supplied certified lower gamma factor with the product of the
certified reversed block factors. It selects the now available certificates,
uses the supplied comparison to rewrite the induced certificate, and applies
the earlier actual lower-to-upper transport. The comparison itself is unproved.

`lConclusion_of_lowerComparison` similarly reduces the upper L conclusion to
the stated divisibility for supplied certified lower and block polynomials.
It selects those polynomials, applies the still unproved comparison, and
transports its exact `Q` and `e` through the earlier transport theorem. These
reductions introduce no additional final-target premise: they expose the
comparison obligations for future analytic work within the unfinished parent
proof. The rank restriction must be used when proving those obligations.

These are internal derived consequences of the imported published theorems,
whose proof modules are the provenance for the analytic and type-preservation
steps. No unrestricted multiplicativity proof or subsequent Section 7 theorem
is used. In particular, factor existence does not imply that the induced gamma
factor equals the product of the block factors, nor does it imply the required
L-polynomial divisibility. Those comparisons remain open. Neither existence
theorem needs a rank inequality, so the dominant-rank boundary `t = r` is retained.
