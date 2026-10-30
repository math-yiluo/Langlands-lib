# Cotangent base-change isomorphism target

For an arbitrary scheme `S`,
`Langlands.GroupScheme.CotangentBaseChangeIsIsoStatement S` is the
proposition that for every scheme `T`, every morphism `b : T ⟶ S`, and
every actual group scheme `G : GroupScheme S`, the specifically
constructed morphism `cotangentBaseChangeMap b G` is an isomorphism.
All schemes lie in a common universe. The map has source
`(Scheme.Modules.pullback b).obj G.cotangentAtIdentity` and target
`((GroupScheme.baseChange b).obj G).cotangentAtIdentity`.

There are no smoothness, flatness, finite-presentation, commutativity,
or abelian-scheme hypotheses. The proposition concerns invertibility
of the canonical map, not the existence of an unrelated isomorphism.
It is a Prop-valued definition and is not proved in this file.

## Source and derivation

Stacks Project Lemma 29.33.10 (tag 01V0) states that the canonical
relative-differential comparison of a base-change square is an
isomorphism for arbitrary scheme morphisms. See `01UM.html` in
registered source `stacks-relative-differentials-internal-hom-2026-10-21`,
content SHA256
`9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`.
Lemma 29.33.8 (tag 01UV) defines this canonical map and characterizes
its value on differentials of local sections. Lemma 29.33.16 (tag 0474)
identifies the cotangent module along a section with the pullback of
relative differentials.

The target here is a derived consequence: pull the differential
comparison back along the identity section of the base-changed group.
A functor preserves isomorphisms. Compose that pulled-back map with
the explicit pullback-composition isomorphism
`cotangentBaseChangePullbackIso b G`. This composite is precisely
`cotangentBaseChangeMap b G` by its definition. The identity-section
compatibility used in that composition is already proved in
`LieBaseChange`. Invertibility of the concrete differential comparison
is also published, as a separate theorem that this file does not import:
`Langlands.Scheme.relativeDifferentialsBaseChangeIsIso S :
RelativeDifferentialsBaseChangeIsIsoStatement S` in module
`Langlands.AlgebraicGeometry.RelativeDifferentialsBaseChangeIsIso` gives
`IsIso (relativeDifferentialsBaseChangeMap f b)` for all `f : X ⟶ S` and
`b : T ⟶ S`, in particular for `f = G.X.hom`.

This target is about the cotangent module. It does not assert that
the internal dual of an arbitrary module commutes with arbitrary
pullback, and it does not claim unrestricted Lie base change.
The proposition is proved, exactly as stated, by
`Langlands.GroupScheme.cotangentBaseChangeIsIso S :
CotangentBaseChangeIsIsoStatement S` in module
`Langlands.AbelianScheme.CotangentBaseChangeProof`. That proof follows the
derivation above. It pulls the published differential comparison back
along the identity section, which preserves isomorphisms, and composes
with `cotangentBaseChangePullbackIso b G`.
