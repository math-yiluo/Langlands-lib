# Near-identity fractions restricted to actual analytic domains

This derived internal unit concerns Berkovich's test relation on analytic
arrows represented by right fractions in the saturated strong localization.
It works over complete ultrametric normed fields, with independent space
and chart universes.

`commonDomainSourceSelection` intersects the two downward-closed locally
refining source selections used for domain factorization. The
canonical maps to the two selections and the full inclusion diamonds
produce numerators on one common source. The strong test relation is
preserved under that source refinement and is equivalent to the test
relation after target-domain inclusion. These identities concern complete
bounded pullbacks.

The generic fraction identification lemma uses a quasi-isomorphism
restricted denominator and the full source and numerator inclusion
squares. After cancelling the new denominator and the monic target-domain
inclusion, the two sides agree by the original denominator equation.
This identifies analytic arrows without inferring equality from points.

For a domain-preserving endomorphism near the identity, restrict the
common fraction denominator to the literal inverse-image domain. Its
point equations show that both numerators on this domain land in the
target domain. Since the second fraction represents the identity, the
entire inverse image of the ambient test locus lies in that source
domain. Thus source-domain restriction preserves the strong test
relation. Simultaneous corestriction then gives near numerators in the
target domain. The full inclusion squares identify their fractions with
the restricted endomorphism and the identity, proving
`IsNear.domainRestrict_id`.

The ingredients are the proved actual-domain, strong test-relation,
source-refinement and right-fraction APIs. This unit is infrastructure for
continuity of restricted invariant-domain actions; it does not assert
the cohomological comparison theorem.
