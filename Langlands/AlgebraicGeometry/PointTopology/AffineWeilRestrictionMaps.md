# Maps of actual affine finite-type Weil restrictions

Worker 105 constructs the actual maps between `affineWeilRestriction A B X`
for morphisms of actual affine finite-type schemes `X` over `Spec B`.
This is derived infrastructure for Conrad, *Weil and Grothendieck approaches
to adelic points* (December 31, 2011), Example 2.4, printed page 3. It uses
the finite-type algebra functor in `RingTheory/WeilRestriction/Functorial.lean`
and the independently constructed point homeomorphism in
`AffineWeilRestriction.lean`.

The rings `A` and `B` are arbitrary commutative rings and `B` is finite
projective over `A`. Each input scheme is affine and its structure morphism
is locally of finite type; affineness makes this full finite type.
`affineWeilRestrictionMap A B f` is the spectrum of the constructed
Weil-restriction algebra map of the actual global-section pullback of `f`.
The algebra and spectrum identity/composition laws prove its identity and
composition laws, with the two contravariances giving the stated covariant
scheme maps.

`affineRingPointEquiv_postcomp_ringTestMap` proves that postcomposition with
an actual spectrum map is exactly precomposition of its algebra map.
`affineWeilRestrictionPointEquiv_coordinates` identifies the representing
point equivalence at every commutative `A`-algebra `T` in the original
scheme's coordinates, with values in the actual tensor product `B ⊗[A] T`.
`affineWeilRestrictionPointEquiv_natural` proves that this equivalence
commutes with every original scheme morphism. Its proof uses the coordinate
identity, the spectrum-map identity, and universal-point naturality.

With topological-ring structures on `A` and `B`, and the canonical
`A`-module topology on `B`, `affineWeilRestrictionPointHomeomorph_natural`
proves the corresponding identity for the actual point homeomorphism.
`weilRestrictionAlgPointEquiv_precomp` is the algebra-coordinate version of
this identity. Both proofs use the same universal-point law, so they fix
the natural map and do not choose an unrelated homeomorphism.

There are no finite-presentation, Noetherian, field, faithful-module,
local-ring, separation or open-unit hypotheses. This unit supplies
functoriality, not the assertion that closed immersions remain closed
immersions. That assertion and representation on arbitrary test schemes
remain separate obligations.
