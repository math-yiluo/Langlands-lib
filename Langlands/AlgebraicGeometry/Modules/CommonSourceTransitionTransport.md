# Transport and common-source changes for overlap identifications

This is derived infrastructure for preserving actual overlap isomorphisms while
extending a line-bundle atlas. It uses `CommonSourceCocycle` and the Library's
canonical pullback composition, equality and identity comparisons. The results
are categorical consequences of those constructions; they make no additional
claim from the literature.

The namespace is `Langlands.Scheme.Modules.CommonSourceCocycle`. All schemes
lie in arbitrary universe `u`, and all objects are actual scheme module sheaves.

The existing `Langlands.Scheme.Modules.compIso f g h w M` identifies
`f* g* M` with `h* M` for a specified equation `w : f ≫ g = h`.
Its hom is the existing `compHom` comparison, and `compHom_naturality`
records naturality in the module using the symmetric form of the published
`Langlands.Scheme.Modules.compHom_naturality`. Given a piece comparison
`e : a* N ≅ M`, `pieceComp` normalizes `f* M` into the specified composite
pullback of `N`. It is an isomorphism. `transition_pieceComp` states that the
transition induced from `N` preserves this normalization. Its proof cancels the
second piece comparison and uses `square_normalize`. `compHom_pieceComp`
identifies a composite of these comparisons with the existing threefold
`pieceNormalize`, by naturality and `compHom_assoc`.

For maps `t : W ⟶ V`, `f : V ⟶ A`, `g : V ⟶ B`, specified composites
`f' : W ⟶ A`, `g' : W ⟶ B`, and an overlap identification `φ : f* Ma ≅ g* Mb`,
`transport` is the actual isomorphism `f'* Ma ≅ g'* Mb` obtained from `t* φ`
by the composition comparisons at its ends. `transport_transition` proves
that transporting a transition from a common module gives exactly the
transition on the prescribed new projections. It has no assumption that `t`
is an isomorphism. The proof cancels the first composition comparison and a
piece normalization; it then applies `compHom_pieceComp`,
`inner_transition_normalize` and `transition_pieceComp`.

The existing `Langlands.Scheme.Modules.pullback_map_injective_of_iso`
provides injectivity on morphisms of pullback along a scheme isomorphism `i`.
Pullback by `i.hom` followed by pullback by `i.inv` is
naturally isomorphic to the identity via the composition, equality and identity
comparisons. Naturality of that isomorphism recovers a morphism from its
pullback. Consequently `transport_injective` says that when `t` is an
isomorphism, equality of transported overlap identifications implies equality
of the original actual identifications. Its proof cancels the composition
comparisons and applies this injectivity to the homs of the two isomorphisms.

For `h : X ⟶ Y`, modules `N` on `X` and `K` on `Y`, and an actual comparison
`e : h* K ≅ N`, `sourceComparison` turns `ea : a* N ≅ Ma` into a comparison
`(a ≫ h)* K ≅ Ma`. It first uses the inverse composition comparison, then
`a* e`, then `ea`. `pieceComp_changeSource` expresses normalization using this
new comparison as normalization into a pullback of `N`, followed by the
pullback of `e.inv` and composition with `h`. Its proof expands these maps,
uses `compHom_assoc`, and moves `e.inv` through the comparison by naturality.
Finally `transition_changeSource` proves that the transitions induced from `K`
with these new comparisons are exactly the old transitions induced from `N`.
It cancels a normalization into `K`, uses the two change-of-normalization
identities, and applies `transition_pieceComp` for `N`.

No openness, covering, finiteness, Noetherianity or rank-one hypothesis occurs
in these results. They provide equalities of actual module-sheaf isomorphisms,
including after changing the common source, rather than a statement about
isomorphism classes. The geometric atlas construction, local extension and
coverage argument for general open-immersion line-bundle extension remain
separate obligations.
