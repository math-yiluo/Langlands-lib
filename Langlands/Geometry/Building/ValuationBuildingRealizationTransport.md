# Transport of an actual valuation-building realization

This is an internal derivation from the existing Library definitions, rather
than a new translation of a literature result. The label “one-group KP
Axiom 4.1.1” refers to the existing `SatisfiesBuildingAxiom` predicate in
`FullValidity.Realization`. Both valuation-building data are supplied for the
same actual group `G` over the same nonarchimedean local field `F : Type u`.
Their reduced buildings and rational-point actions are the existing ones.
No existence of those data or of a source axiom witness is asserted.

The generic lemma
`AffineRootSystem.isFaceOf_image_transportedRoots_iff` preserves and reflects
the sign-defined affine-root face relation under an affine equivalence.
Its proof uses the existing transport identities for full facets and facet
closures, and cancels images under the injective equivalence. The vector
spaces and affine torsors in this lemma have unrestricted universes.

`PolysimplicialRealization.transport` takes a supplied building isomorphism
`Φ` between the two actual quotients. It retains the source factor index,
vertex sets and polysimplicial complex, and composes the source realization
with `IsBuildingIso.facetEquiv`. Thus every realized facet is its full image
under `Φ`. Injectivity of `Φ` identifies the apartment subcomplex of `Φ '' Y`
with the original apartment subcomplex of `Y`.
`transport_apartments` uses preservation and reflection of apartments by the
building isomorphism to prove equality of the two sets of combinatorial
apartments.

For the remaining geometric transport, the hypotheses are:

- `Φ` commutes with the action of every element of the same group `G(F)`;
- an affine equivalence `e` identifies the canonical apartment maps;
- the image of the entire affine-root set under inverse precomposition by
  `e` is exactly the target affine-root set.

The equivariance premise makes images commute with the pointwise set action.
`transport_isPolysimplicialAction` retains each source vertex automorphism;
its condition on realized facets follows by cancelling set images under `Φ`.
`image_translatedApartmentMap_of_comparison` identifies corresponding
translated facet images. Applying the generic affine-root face lemma in both
directions then proves `facetPrecedes_facetEquiv_iff` for the existing
`FacetPrecedes` relation. The reverse direction explicitly pulls target
apartment facets back by `e.symm`. This gives `transport_isFaceCompatible`.
Equality of the canonical apartment images needs only the apartment-map
square and surjectivity of `e`, as recorded separately.

The actual torus clauses require additional data: an isomorphism
`σ : B₁.S ≅ B₂.S` with
`B₁.i = CommGroupScheme.groupHom σ.hom ≫ B₂.i`. This is a hypothesis about
the actual embedded maximal split tori, beyond the building isomorphism.
`normalizerPoints_eq_of_torusIso` specializes the existing actual
normalizer-transport theorem to the identity isomorphism of `G`.
`conjTorus_eq_of_torusIso` identifies the actual conjugate subgroup functors
using invariance of the range under an isomorphism of the source.
`isTorusChart_of_torusIso` transfers an actual torus chart by composing its
torus isomorphism with `σ.symm`; the inverse embedding square comes from
`torusTransport_inverse_square`.

`hasTorusApartmentCorrespondence_of_comparison` transfers both clauses of
the supplied source correspondence. Existence of charts uses that explicit
composition. The equivalence between equality of conjugate tori and equality
of translated apartments uses the equal conjugate subgroup functors,
equivariance of `Φ`, equality of the canonical apartment images and
injectivity on set images. `hasNormalizerApartmentStabilizer_of_comparison`
reflects stabilization of the canonical apartment through `Φ`, applies the
source stabilizer clause and rewrites the actual normalizer equality.

Finally, `PolysimplicialRealization.transport_satisfiesBuildingAxiom`
assembles all five fields of the existing one-group predicate.
Face compatibility and the polysimplicial action use the preceding
lemmas. The combinatorial building witness is the source witness after
rewriting the equality of apartment sets; its complex is unchanged.
The torus correspondence and normalizer stabilizer use the actual torus
comparison above.

Every comparison hypothesis and the source `SatisfiesBuildingAxiom` witness
remain premises. This unit neither supplies actual building data, root
filtration comparisons or the source building witness, nor proves
`RootValuationBuildingConstructionStatement` or the other requested KP
axioms. It supplies conditional transport of the one-group building axiom
for the existing quotients, at every universe `u`.
