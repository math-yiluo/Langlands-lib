# Canonical coherence of local internal-Hom pullback

The theorem `Langlands.Scheme.Modules.localHomPullbackCoherence` proves exactly
`LocalHomPullbackCoherenceStatement` from
`ModuleLocalHomPullbackCoherenceStatements`. Its two components are
`localHomPullbackIdentity` and `localHomPullbackComposition`. They concern the
fixed published `localHomPullback` for arbitrary schemes and module sheaves,
without extra hypotheses. This module does not construct the global dual
comparison or prove the separate restriction and scalar laws.

## Identity

The helper `pullback_square_identity` uses Mathlib's left and right
pseudofunctor unit laws. After eliminating the equation identifying a map with
an identity, the proof cancels a `pullbackComp` isomorphism and reduces the
remaining equality transports to identities. The helper
`pullback_restrict_square_identity` inserts the natural isomorphism from
restriction to pullback along the open immersion; naturality moves its inverse
past the identity comparison and the two restriction comparisons cancel.

Specializing this calculation gives `restrictPullbackNatIso_identity`: the
canonical restriction/pullback comparison for the identity, followed by
`pullbackCongr (morphismRestrict_id U)` and `pullbackId U.toScheme`, is restriction
of `pullbackId X`. The proof is factored into a generic scheme square to avoid
unfolding the definitionally equal identity inverse-image opens during rewriting.

`localHomPullbackIdentity` applies the injectivity of
`internalHomSectionsEquiv`. This changes the claim into an equality between
maps of restricted module sheaves. The defining local-pullback formula and
naturality of the section equivalence reduce it to conjugation by the
isomorphisms in `restrictPullbackNatIso_identity`. The generic conjugation
helper cancels an isomorphism on the right and uses naturality of the identity
pullback comparison.

## Composition

`pullbackSquareHom` is the pullback comparison attached to a commutative square:
`pullbackComp` along one path, transport through the square equation, and the
inverse of `pullbackComp` along the other path. Composing it with the comparison
for the latter path gives the former comparison.

The composition calculation uses the published `compHom` and `compHom_assoc`
helpers from `Picard.RigidifiedPullbackProofs`. These are categorical lemmas for
arbitrary scheme-module pullbacks; no Picard or line-bundle hypothesis is used.
Three instances of their associativity identity compare the three sides of two
adjacent commutative squares. After cancellation of the final isomorphism,
functoriality combines the intermediate maps, and the two individual square
identities reduce the claim to the third associativity identity.

`pullbackRestrictSquareHom_composition` inserts the natural isomorphisms from
restriction functors to pullback along the three vertical maps. The middle
isomorphism and its inverse cancel. Naturality of `pullbackComp` moves the final
restriction comparison across the composition comparison, and naturality of
the initial restriction comparison finishes the equality.

Specialization to open immersions gives `restrictPullbackNatIso_composition`.
Here `morphismRestrict_comp` identifies the restricted composite with the
composite of restricted morphisms, and `pullbackCongr` transports along that
actual equality. This specialization and the final local-map theorem use a
finite heartbeat limit of 800000 because kernel checking the inverse-image
open identifications is expensive.

Finally, `localHomPullbackComposition` again uses the injectivity of
`internalHomSectionsEquiv`. Expanding its local-pullback formulas gives a
successive conjugation. A generic natural-isomorphism calculation identifies
that conjugation with the one for the composite, using the two instances of
`restrictPullbackNatIso_composition` for the source and target modules. The
result is exactly the conjugation by the actual `pullbackComp f g` components
specified in the target. Pairing the two component theorems proves
`localHomPullbackCoherence`.
