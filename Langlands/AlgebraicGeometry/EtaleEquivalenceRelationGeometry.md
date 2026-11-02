# Structural morphisms of an étale equivalence relation

Author: Worker 706.

This internal construction makes explicit the structural maps already determined
by the published `EtaleEquivalenceRelation` axioms. It supports the presentation
version of the stratification used in Stacks Project Lemma 68.8.3 (Tag 0BBN) and
Lemma 68.8.6 (Tag 07ST). The registered sources are
`stacks-stratification-2026-11-02`, `0BBN.html`, and
`stacks-noetherian-approximation-2026-11-01`, `07ST.html`.
Cartesian morphisms use the convention of Tag 0APD in
`stacks-etale-equivalence-relations-2026-11-01`.
These elementary structural constructions are derived from the Library
definition; they do not assume any approximation theorem or quotient.

All declarations are in
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelation` and preserve the arbitrary
scheme universe `u`.

`hom_ext` states that two maps into the relation scheme agree if both endpoint
maps agree. It follows by cancelling the monomorphism `(t,s)` and using the
universal property of the absolute product.

`unit` chooses the reflexivity map for the identity of the object scheme.
`unit_t` and `unit_s` record its endpoints. `inverse` chooses the symmetry map
for the identity of the relation scheme. `inverse_t` and `inverse_s` exchange
its endpoints. Applying `hom_ext` proves `inverse_inverse`, so `inverseIso`
packages reversal as an involutive isomorphism.

`composition` chooses the transitivity map on `R ×_{s,U,t} R`.
`composition_t` and `composition_s` record its endpoints.
`compose a b h` composes any pair of composable maps into `R`, in the order
`(x,y)` followed by `(y,z)`; its endpoint formulas are `compose_t` and
`compose_s`. The unit, associativity, and inverse laws
`compose_unit_left`, `compose_unit_right`, `compose_assoc`,
`compose_inverse_right`, and `compose_inverse_left` follow by comparing
endpoints. Thus the existential axioms supply actual groupoid operations
without additional mathematical hypotheses.

`inverse_naturality` proves that an endpoint-preserving pair of maps commutes
with reversal. `isCartesianHom_id` and `IsCartesianHom.comp` give the identity
and composition laws for the published cartesian-morphism predicate, the
latter by pasting pullback squares. `IsCartesianHom.isPullback_t` transports
the source pullback square across the two reversal isomorphisms, giving the
target pullback square.

`isAffine_relation` records that, if `U` is affine and `(t,s)` is a closed
immersion, `R` is affine. A product of affine schemes is affine, a closed
immersion is affine, and an affine morphism to an affine scheme has affine
source.
