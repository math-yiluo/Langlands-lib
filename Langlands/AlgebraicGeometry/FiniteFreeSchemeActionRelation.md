# The equivalence relation of a finite free scheme action

This internal helper constructs the disjoint union of the graphs of a group
action on a scheme. The action convention is
`act g ≫ act h = act (g * h)`. Freeness means that, for every morphism from a
nonempty scheme, the resulting maps obtained by applying different group
elements are distinct. The group and the scheme have the same arbitrary
universe. The structure name anticipates the finite-group application, while
finiteness is a separate hypothesis on the constructions that need it.

`relationScheme`, `source`, and `target` are the coproduct of copies of the
original scheme, its fold map, and the action maps. `ι_source` and `ι_target`
record their restrictions to each summand. Both projections are étale because
each restriction is an isomorphism and étaleness is local at the source.

`reflexive` uses the identity summand. `reverse` applies the action and then
uses the inverse label. Its two endpoint identities prove `symmetric`.

For a finite group, `composableScheme` is the coproduct, over pairs of group
elements, of the corresponding pullbacks. `composableLeft` and
`composableRight` exhibit it as the pullback of the relation projections by
Mathlib's finite extensivity theorem. `compose` uses multiplication of the
labels. Its endpoint identities follow from the pullback equation and the
action law. `transitive` lifts an arbitrary composable pair through this
pullback. Thus the witnesses apply to maps from disconnected schemes as well.

For a separated scheme, each action graph is a closed immersion: it is the
diagonal followed by the product of the action automorphism and the identity.
Hence the entire graph coproduct is surjective on stalks, a
property local at the source. `fieldPoint_injective` factors each field-valued
point through an actual summand using the published
`connectedHom_factor_coproduct`. Equality of sources identifies the maps to the
original scheme, and freeness then identifies the labels. Mathlib's
field-valued criterion gives universal injectivity; injectivity on underlying
points together with surjectivity on stalks gives actual monicity.

The intended application is the free symmetric-group action in the first proof
paragraph of Stacks Lemma 68.8.3 (Tag 0BBN), registered source
`stacks-stratification-2026-11-02`, directory SHA-256
`844f29708bb7e14d69fe37b2251bb94ea49065647c1257aaaeb4655ac6a1288e`.
The generic relation construction is derived here, rather than a transcription
of the full lemma.

All these constructions and proofs are derived here from the coproduct,
pullback, and scheme-morphism APIs in the pinned Mathlib and the published
connected-source factorization helper. This pair does not construct a
quotient, establish finiteness of the projections, or prove the Noetherian
first-level theorem.
