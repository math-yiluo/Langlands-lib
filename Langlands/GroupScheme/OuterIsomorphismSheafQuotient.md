# Exact outer orbits from represented fppf action quotients

This internal construction derives exact all-test orbits from the published
fppf action-quotient and isomorphism-scheme interfaces. It assumes a represented
quotient with an actual flat, surjective, quasi-compact class morphism; it does
not establish quotient representability or reductive-group geometry.

For any action free on all relative tests, the published
`ActionQuotientOrbitRelation.orbitSieve_mem` gives local acting points whenever
two points have the same quotient image. Freeness identifies their restrictions
on overlaps. The fppf sheaf condition for the acting scheme glues them to a
point on the original test. The sheaf condition for the acted-on scheme
descends its action equation. Freeness also proves uniqueness.

A faithful automorphic action acts freely on a supplied actual isomorphism
scheme by inverse precomposition. Equality of the two transformed families
on every refinement, followed by cancellation of the family of group
isomorphisms, identifies the two inverse acting points by faithfulness.

`GroupIsomorphismScheme.outerOfFppfActionQuotient` keeps the supplied class
scheme and its fpqc class morphism. The quotient coequalizer identity proves
invariance; the preceding gluing result proves the exact unique-difference
property on every relative test, including nonreduced tests. No global lift
through the original group scheme is assumed.
