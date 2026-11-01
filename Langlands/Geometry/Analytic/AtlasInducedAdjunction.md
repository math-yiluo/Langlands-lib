# Induction adjunction on full nonempty-chart atlas action categories

Author: Worker 56. Namespace: `Langlands.Analytic.AtlasInducedAction`.

Let `K : Type u` be a complete normed ultrametric field, `G : Type z`
a group, and `H` a subgroup. All presentations use
`AffinoidAtlasPresentation.{u, max z v, max z w} K`; these universes
accommodate arbitrary coset-indexed copies. Objects of
`NonemptyAtlasAction K H` and `NonemptyAtlasAction K G` are supplied
categorical actions for which every original chart has nonempty bounded
multiplicative spectrum. Their morphisms are all original complete
equivariant chosen atlas arrows. Charts may overlap or nest. Empty spaces
with no charts and infinite-index subgroups are allowed. No topology on
the group, openness or joint-action continuity is required in this module.

`copies_hasNonemptyCharts` applies the existing disjoint-union spectrum
condition to the actual coset-copy atlas. `nonemptyCopiesFunctor` then
lifts the existing `copiesFunctor`, after the full inclusion of the source
category, to the target nonempty-chart category. Its objects and maps are
precisely the already constructed `copiesAction` and
`copiesEquivariantMap`; it introduces no assumed induction object.
`NonemptyAtlasAction.restrict H.subtype` is the previously constructed
restriction functor, which retains the supplied presentation and bounded
arrows exactly.

For a source `X` and target `Y`, `nonemptyHomEquiv` constructs

`Hom_G(nonemptyCopiesFunctor H X, Y) ≃ Hom_H(X, restrict H.subtype Y)`.

The forward map unwraps the full-subcategory arrow, uses the constructed
relative `actionExtensionEquiv`, then precomposes with
`(normalizationIso X).inv` to start at the original source. The inverse
first composes the supplied original-source arrow with
`(normalizationIso X).hom`, uses the constructed full bounded extension,
and wraps it as a full-subcategory arrow. The two inverse laws cancel
these actual isomorphisms and use the existing restriction/extension
inverse laws. The application lemmas expose exactly these maps.
The chart condition on `X` supplies the normalization inverse; no inverse
to empty-chart deletion on arbitrary presentations is assumed.

The full-arrow naturality of the relative correspondence and inverse
normalization prove source naturality. Target naturality follows from
that of the relative correspondence and associativity. Injectivity and
the inverse laws give source naturality of the inverse correspondence.
`nonemptyAdjunction` packages these data with `Adjunction.mkOfHomEquiv`
as an actual adjunction from `nonemptyCopiesFunctor H` to restriction.
`nonemptyAdjunction_homEquiv` proves that its Hom correspondence is exactly
the one constructed here. Thus the adjunction includes the unit, counit
and triangle identities supplied by Mathlib from these proved natural
bijections.

The provenance is internal categorical assembly of the already constructed
coset-copy action, full bounded extension, and conditional natural
normalization isomorphism. Every naturality equation is an equality of
complete equivariant arrows, retaining chosen chart indices and bounded
pullbacks. No equality of algebra maps is inferred merely from their
point maps. This is an adjunction of the stated chosen-presentation
categories. Quotient transport with continuous inputs, continuity into
the analytic automorphism topology, refinement localization, general
analytic sites and Harris tower specialization remain separate.
