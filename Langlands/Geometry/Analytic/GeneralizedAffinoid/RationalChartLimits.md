# Finite limits of actual positive-radius rational charts

Authors: Worker 56 and Worker 36. The pullback-cone packaging follows
Worker 36's published `StrictTestDomain.RationalLimits`; the lift here
uses the published weighted bounded pushout rather than a locus inclusion.
Worker 965's `GeneralizedAffinoid.RationalIntersectionUniversal` is imported
for that pushout construction.

Fix a complete ultrametric normed field K and a presented affinoid algebra
A. The objects are the existing chosen `RationalChart K A`, with finite
numerator tuples, arbitrary positive radii, scalar-series coefficient
representatives and explicit unit generation of their classes in A.
Their algebras are the actual closed rational quotients. An arrow
`c → d` is an actual bounded K-algebra map `d.algebra → c.algebra`
whose composite with the structural map from A is `c.baseMap`.

For actual arrows `f : c → d` and `g : c → e`, the two bounded maps
agree on A: both composites are `c.baseMap`. `interLift f g` applies
the published `RationalIntersection.pushoutLift` to this agreement.
Its source algebra is the all-products intersection quotient underlying
`d.inter e`, and its target algebra is `c.algebra`. The latter is complete
and ultrametric by the existing quotient construction and completeness
of K. The imported lift constructs its product fraction tuple and derives
the uniform weighted monomial bound from the actual bounded maps.
`pushoutLift_comp_base` and f's structural equation prove the required
equation over A, so the result is an actual chart arrow.

`interLift_interLeft` and `interLift_interRight` identify its two
projection composites with f and g. They use the already proved
uniqueness of actual restrictions over A, derived from unit generation
and bounded-map extensionality on the base. This proves equations between
constructed bounded maps; no thin-category assumption or existence of
an arrow from a locus inclusion is an input.

`interBinaryFan d e` has vertex `d.inter e` and the existing bounded
projections `interLeft` and `interRight`. `interBinaryFanIsLimit` uses
`interLift` for each binary fan, the two projection equations for
factorization, and restriction uniqueness for uniqueness of the lift.
It therefore proves a product universal property in the actual chart
category.

For any cospan `d → b ← e`, `interPullbackCone` has the same vertex
and projections. Its square commutes because the two composites to b
are actual parallel restrictions and hence equal. Any cone supplies two
actual arrows to d and e, so the same `interLift` constructs its lift.
`interPullbackConeIsLimit` proves the two factorization equations and
uniqueness. The common-target compatibility of an arbitrary cone is
automatically satisfied by the proved uniqueness of restrictions.

The instances `hasLimit_pair`, `hasBinaryProducts`, `hasLimit_cospan`
and `hasPullbacks` expose these constructions to Mathlib. `hasTerminal`
uses the previously constructed empty-numerator whole chart and its
proved terminal property. `hasFiniteLimits` applies Mathlib's theorem
that a category with a terminal object and pullbacks has finite limits.
Thus the finite-limit existence assertion is deduced from explicit
quotient constructions and their proved universal properties.

These are limits over the fixed base A in the category of chosen
rational charts. In particular a binary product here represents
intersection of their loci in the base, not the product of arbitrary
affinoid spaces. Empty numerator tuples and spectra, zero and
nonreduced quotient algebras, trivial valuations and arbitrary positive
radii remain allowed. This construction does not prove representation
of arbitrary locus inclusions, full analytic-domain spectral-image
factorization, sheafness, analytic atlases or etale sites.

Source context: Berkovich, *Non-archimedean analytic spaces*, Trieste
lectures (2009), printed/PDF p.8, Definition 2.1.11 for bounded maps and
the opposite affinoid-space direction; p.9, Definition 2.2.1 and Exercise
2.2.2(ii)–(iii) for positive-radius rational quotients and intersections;
p.10, Fact 2.2.3(i) for the representing spectrum. Registered source
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The categorical universal properties and finite-limit instances here
are internal consequences of the published bounded pushout, chart
category and whole chart, rather than separately numbered source
claims. Explicit unit generation is retained without asserting an
equivalence with the source's absence of common spectral zeros.
