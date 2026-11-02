# Exact-degree schemes and their trivial self-correspondences

This derived helper continues the symmetric tuple construction in Stacks
Lemma 68.8.3, Tag 0BBN, registered as
`stacks-stratification-2026-11-02` (snapshot `0BBN.html`, proof). It uses
the preceding unit-locus module to turn its pointwise unit containment
into a scheme-theoretic pullback statement.

Let the étale equivalence relation have separated source map and affine
object and relation schemes. The factorization and pullback assertions
also assume that its joint endpoint map is closed. All constructions allow
an arbitrary universe `u`.

`tupleSymmetricCross_factors_unit_of_not_threshold` states that any
self-correspondence on a test scheme factors through the unit when its
left endpoint avoids the next threshold at every point. The preceding
point-containment theorem puts its image inside the open unit image.
The universal property of an open immersion then supplies the factorization.
Composing with the left endpoint identifies the factor with that endpoint.
This proof works on arbitrary test schemes, including nonreduced ones.
`tupleSymmetricCross_endpoints_eq_of_not_threshold` follows by composing
the factorization with the right endpoint.

`tupleSymmetricCross_unit_isPullback_of_not_threshold` gives the associated
cartesian square for any map `d : T → Xₙ` avoiding the next threshold:
the pullback of the left endpoint of the symmetric self-correspondence
along `d` is `T`, with map to the correspondence `d ≫ unit`.
The proof verifies the universal property. Given compatible maps into
the correspondence and `T`, the factorization theorem identifies the first
map with the unit of the second; uniqueness follows from the identity
projection to `T`.

`tupleSymmetricDegreeScheme` is the closed subscheme of the symmetric tuple
scheme defined by the vanishing ideal of `tupleSymmetricDegreeClosed`.
`tupleSymmetricDegreeι` is its canonical inclusion. The module proves that
this inclusion is closed, that its source is affine, and that its range is
exactly the complement of the next threshold. The pointwise exclusion
theorem records the latter consequence for each point of the degree scheme.
The construction uses Mathlib's ideal-sheaf subscheme construction; no
reducedness instance is needed by the proofs here.

`tupleSymmetricDegree_unit_isPullback` specializes the general cartesian
square to this inclusion. `tupleSymmetricDegreeCrossIso` is its canonical
isomorphism from the degree scheme to the left-endpoint pullback.
The two `hom_fst` and `hom_snd` formulas identify its projections, and
`inv_eq_snd` identifies its inverse with the projection to the degree scheme.

These conclusions provide an actual scheme and the triviality of its
self-correspondence over the exact-degree locus. They do not by themselves
prove the Noetherian first-level statement.
