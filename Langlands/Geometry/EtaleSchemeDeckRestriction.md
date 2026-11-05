# Agreement of canonical scheme deck actions with étale restriction

This internal comparison identifies the arbitrary-morphism construction in
`EtaleSchemeDeckAction` with the earlier construction in `EtaleDeckAction`
when the original structure map is étale. The original scheme, base coefficient,
group action, and specified recovery maps are retained.

## Inputs and conventions

Let `X` and `Y` be schemes, `p : Y ⟶ X` étale, and `R` a commutative ring.
Schemes, the ring, and its module coefficients share universe `u`.
Let `G : Type t` be a group, with arbitrary independent universe `t`, and let
`τ : G →* (Aut Y)ᵐᵒᵖ` be the original automorphism homomorphism. The actual deck
triangles are `hp : ∀ g, (aut τ g).hom ≫ p = p`.

The coefficient comparisons use only this geometry. All three consumer
isomorphisms, their underlying formulas, and their recovery squares assume
`HasDerivedCategory.{wY} (ModuleSheaf Y R)` and
`HasDerivedCategory.{wR} (ModuleCat.{u} R)`, with independent sizes `wY` and `wR`.
These assumptions are retained for ordinary cohomology and sections because
the new deck actions and their recovery are inherited from the derived
construction. No derived-category instance on sheaves over `X` is needed.
The ordinary restricted degree-zero comparison alone needs neither instance.

## Coefficient comparison

The imported `EtaleCohomologyAction.restrictionCongr_hom_component` gives the component of forward restriction
transport along an equality of scheme maps as the presheaf map of the inverse
site transport. It complements the published inverse-component lemma.

`restrictionCoefficient_act` proves that the earlier deck coefficient action
is precisely restriction composition along `p` and the original automorphism,
followed by restriction transport along `hp g`. Its proof first replaces
restriction equality transports by their site components; the remaining
maps reduce to composition of presheaf maps.

`projectionInverseImageIso_restriction` applies to any étale triangle
`f : Z ⟶ Y`, `q : Z ⟶ X`, `hf : f ≫ p = q`, with `q` also étale. It compares the
constructed inverse-image triangle with restriction composition and transport
along the same equality. This follows from the published composition and
equality coherence of `inverseImageIsoRestriction`.

Writing `βp` for `inverseImageIsoRestriction p R`, `a` for `(aut τ g).hom`,
`c` for the new `coefficientIso`, and `d` for the old deck coefficient action,
`coefficientIso_restriction` specializes the triangle result to the equation

```
c_M ≫ βp_M = inverseImage(a).map βp_M ≫ βa_(restriction(p)M) ≫ d_M.
```

The maps in this square are constructed from the original geometric triangles;
no compatibility of cohomology is supplied as an assumption.

## Three equivariant natural isomorphisms

`derivedRestrictionIso` identifies `derivedFunctor τ p hp R` with
`deckDerivedSectionsFunctor R τ p hp`. Its component is derived sections of
`βp_M`. Equivariance follows from the coefficient square, the source and target
naturality of actual geometric pullback with coefficients, and the existing
comparison with étale restriction. Coefficient naturality is the naturality of
`βp` after applying derived sections.

`cohomologyRestrictionIso n` identifies the new ordinary-cohomology deck
functor in each nonnegative degree with `deckCohomologyFunctor`.
`sectionsRestrictionIso` identifies the new section deck functor with
`deckSectionsFunctor`. They are constructed from the derived comparison through
the specified homology and derived degree-zero recovery isomorphisms on both
sides. Their component-formula theorems prove that they are respectively
ordinary cohomology and sections of `βp_M`; the formulas use naturality of the
actual canonical recovery isomorphisms and cancellation of their inverses.
Thus all three isomorphisms are equivariant and natural in every base sheaf,
with the specified underlying coefficient maps.

## Recovery squares

`derivedRestrictionIso_homology` and `derivedRestrictionIso_zero` are equalities
of full equivariant natural transformations. They say that applying homology
to the derived comparison and then using the old recovery equals using the
new recovery followed by the ordinary or section comparison.

`restrictionCohomologyZeroIso` is the inherited old ordinary degree-zero
recovery, obtained by whiskering `pullbackCohomologyZeroFunctorIso` by the old
deck coefficient functor. Its underlying formula is exactly the original
canonical `cohomologyZeroIso` on the restricted sheaf.
`cohomologyRestrictionIso_zero` proves that the new and old ordinary degree-zero
recovery maps commute with the cohomology and section comparisons. The proof
reduces to naturality of `cohomologyZeroIso` for `βp_M`.

## Provenance and scope

This is an internal coherence construction from the existing actual
inverse-image, étale-restriction, geometric coefficient pullback, and equivariant
derived-section definitions; it claims no additional external source theorem.
The auxiliary equalities establish the displayed constructions and formulas.

The unit compares the three functors in the base coefficient for fixed original
deck geometry. It does not compare arbitrary maps between two such geometries,
nor construct a category of all raw deck geometries. No covering, torsor,
freeness, topological continuity, smoothness, compact support, properness, or
finiteness property is asserted. Analytic-étale realization, arithmetic tower
identifications, and the Harris/Shimura specialization remain obligations of
the broader framework.
