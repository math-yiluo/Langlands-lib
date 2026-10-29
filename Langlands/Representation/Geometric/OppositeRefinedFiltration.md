# Reversed upper filtrations in the composed opposite Jacquet quotient

Worker 514 constructs an internal adapter for actual object filtrations. For
an arbitrary representation `A` of `GL_n(F)`, a block shape `B`, a refinement
`S`, and a supplied finite filtration of the normalized upper Jacquet module
of `A` along `B.reverse`, it constructs a filtration of the actual
`T.normalizedComposedOppositeJacquet B S A.ρ`. The field and representation
carrier universes remain independent. No smoothness, admissibility,
irreducibility, positive-rank or finite-length assumption is needed for these
constructions.

`oppositeFiltrationOfReverse` first pulls the given filtration back along
`OppositeCuspidalJacquetFiltration.leviReverseEquiv B`, then transports it
through the published actual `oppositeJacquetReverseEquiv T B A`. That
equivalence already retains the normalized modulus factors. The membership
formula uses its inverse, and `oppositeFiltrationOfReverseGradedEquiv`
identifies the original pulled-back grade with the new grade at the same
index.

`oppositeRefinementFiltrationEquiv` chooses the equivalence supplied by the
published `Parabolic.normalizedOppositeRefinementTransitivity`. Its proved
quotient-representative formula sends the iterated class of a vector to its
direct composed class; the adapter exposes that same formula.
`composedOppositeFiltrationOfReverse` takes the existing actual
`normalizedRefinedOppositeJacquetFiltration` of the preceding opposite
filtration and transports it through this transitivity equivalence.
Membership means precisely that the inverse transitivity image has a
representative in the corresponding opposite step. The intermediate image
grade and the final composed grade are equivalent at the same index.

All filtrations retain the supplied length, order and endpoints. The
construction uses actual invariant subspaces, their images under the actual
Jacquet quotient maps, and equivalences of the actual normalized quotient
representations. Its provenance is internal composition of the published
reversal, object-filtration transport, opposite image-filtration and opposite
transitivity constructions. It introduces no new source-derived
representation-theoretic assertion.

For the supported excess-multiplicity task, a later specialization can take
`A` to an actual normalized outer induction and the input to its geometric
support-image filtration. This module does not construct that geometric
filtration, identify its geometric pieces or its coarse Weyl contribution,
detect a noncoarse branch from multiplicity excess, or prove continuation.
Exactness-based comparisons of the intermediate image grades with Jacquet
modules of the original grades are also separate from the transport
equivalences constructed here.
