# Applying the pole criterion to automorphic classes

Author: Worker 422.

`HaveSameLowerRankPoleOrders` is an internal predicate recording certified
class-level pole tests. For two automorphic objects of rank `n + 2`, it asks
for equal pole orders of certified pair L-polynomials against every essentially
square-integrable automorphic object of each rank `r + 1` with `r ≤ n`,
at the specified nontrivial additive character and supplied self-dual measure.
Both tested objects and all test objects lie in the same carrier universe `uA`.

This supporting helper module transports the existing representation-side
`SquareIntegrablePoleOrderCharacterizationStatement` to the automorphic class
space used in assembly characterization. The criterion is an explicit
hypothesis, not a proved input. The module proves neither its analytic and
classification content nor the full assembly characterization. The field and
automorphic carrier universes remain independent.

`exists_automorphicObject_equiv` applies the published
`padicIrreducibleSmoothSmallRealization` to an irreducible admissible smooth
representation. It transports admissibility across the resulting actual
equivalence and bundles the realization as an automorphic object in any
specified carrier universe.

`isAdmissible_of_essentiallySquareIntegrable` chooses the real exponent from
the existing essential square-integrability predicate. Square-integrability
implies admissibility of the twisted representation. The determinant norm
has open kernel, hence so does its real-power character; the published
admissibility equivalence for that twist gives admissibility of the original
representation.

`automorphicClass_eq_of_pole_order_tests` assumes the representation-side
criterion at block universes `uA, uA`, one nontrivial additive character, and one
supplied self-dual Haar measure. Its first object is assumed non-supercuspidal.
It requires equal pole orders for certified class L-polynomials against every
essentially square-integrable automorphic object of each lower rank.

The proof first realizes the two given objects in the criterion's carrier
universe `max uF uA`. For each irreducible essentially square-integrable test
representation in that universe, the preceding lemmas produce an equivalent
automorphic object in `uA`. Essential square-integrability transports through
that equivalence. The assumed class tests therefore supply the two
polynomials. The published `isAutomorphicPairLPolynomial_iff` transports their
certificates to the fixed larger representatives of the original objects
and the supplied test representation. All pair-polynomial relations keep
the same block universes `uA, uA`; no transport of these relations between
different block universes is asserted or used. The assumed criterion then
gives an equivalence of the two larger representations. Composing with the
chosen realization equivalences proves equality of the original classes.

These lemmas are internal consequences of the published definitions and
proved realization, equivalence, admissibility and twist APIs. The motivating
application is Henniart 2002, section 4.5, printed page 600 (registered source
`henniart-2002-characterization`). The assembly's lower-rank test coverage and
non-supercuspidality remain separate obligations for that application.
