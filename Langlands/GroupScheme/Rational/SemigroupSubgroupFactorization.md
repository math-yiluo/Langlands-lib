# Exact ordered semigroup products from compatible actual subgroup factors

The first construction works over an arbitrary base scheme `B` in universe
`u`. Let `i : N ⟶ P` be a group-scheme map whose underlying morphism is a
monomorphism, and let `j : K ⟶ P` be another group-scheme map. Suppose the
all-test subgroup image of `i` is normalized by the image of `j`.
The existing normalized-conjugation construction gives the actual action of
`K` on `N`. Its equation after composition with `i` is
`normalizedSubgroupAction_comp`.

If the original normal-factor-first map `subgroupMultiplication i j` is an
isomorphism of schemes over `B`, `normalizedSubgroupFactorIso` constructs a
group-scheme isomorphism from this actual semidirect product to `P`.
Its underlying scheme map is precisely the original multiplication.
The construction specializes `AutomorphicAction.semidirectFactorIso` to
the existing normalized-conjugation action.

Let an external group `L` act on `P`. Suppose its action preserves the
all-test image of `i` and fixes every point in the image of `j`.
Restricting the external action to the represented image of `i` gives
an actual external action on `N`. The two actions on `N` commute:
apply the external action to the conjugation equation, use fixedness
of the acting factor, and cancel the monomorphism `i`.
Consequently the recovered factorization intertwines the semidirect lift
of this restricted action with the original external action. These
equations hold over every test scheme, including nonreduced tests.

The ordered-product theorem specializes to any field `k` and a split
torus `S` acting externally. It assumes that `K`, `N` and `P` are affine,
that `K` and `N` are smooth and connected, the same normalization,
stability, fixedness and multiplication isomorphism hypotheses,
`SemigroupFunctorialityStatement`, `SemigroupIntersectionStatement`, and
the exact ordered-product property for the restricted action on `N`.
It concludes `HasOrderedSemigroupProducts` for the original action on `P`.
Apply `hasOrderedSemigroupProducts_semidirect` to the two constructed
commuting actions, then transport through the equivariant isomorphism.
The original block-versus-other-positive-closure exclusion, occurring
zero weights, original ordering and empty index case are those of the
unchanged product predicate.

The provenance is internal: this unit assembles the published normalized
conjugation, represented stable-subgroup actions, actual semidirect
factorization and equivariant ordered-product transport. It constructs no
decomposition of an arbitrary solvable group and proves neither scalar
descent nor the full `SemigroupOrderedProductStatement`. Existence of the
stated factors and multiplication isomorphism remains an explicit premise.
