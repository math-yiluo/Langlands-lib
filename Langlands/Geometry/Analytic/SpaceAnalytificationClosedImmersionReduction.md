# Closed immersion analytification reduced to affine closed embeddings

This internal contribution proves a reduction of the unchanged all-universe
`SpaceAnalytificationImmersionStatement` to the affine closed embedding input.
`AffineClosedEmbeddingProperty K` asserts that for finite polynomial presentations
of any two `K`-algebras in universe `u`, every surjective algebra map induces a
closed embedding on the underlying spaces of their localized affine
analytifications. This is an explicit premise, not a theorem proved in this module.
`affineClosedEmbeddingProperty_of_statement` extracts it from the first clause of
the existing `AffineAnalytificationImmersionStatement`.

`SpaceAnalytificationImmersionReductionStatement` says that if this affine property
holds for every complete ultrametric nontrivially normed `K : Type u`, then the exact
published algebraic-space immersion statement holds in universe `u`.
`spaceAnalytificationImmersionReduction` proves the reduction. It does not discharge
the affine premise, prove the unconditional full target, or assert task completion.
All fields and analytic category universes are the arbitrary same universe `u`.

## Algebraic closed pullbacks

`exists_closed_affine_test_pullback` pulls the closed immersion back along an affine
test map `Spec A → X`. Its representing scheme `V` is a closed subscheme of `Spec A`,
so it is affine and locally of finite type over `Spec K`; finite polynomial
presentation of `A` supplies finite type over `K`. The actual coordinate algebra
`C` is finite type. The canonical affine isomorphism over the specified base gives
an algebra map `φ : A → C`, a test point `z : X′(C)` and the original presheaf
pullback square. The spectrum map of `φ` is a closed immersion. Surjectivity on
global sections, compared with `φ` by the naturality of the canonical `Γ(Spec)`
isomorphism, proves that `φ` is surjective. No analytic premise enters this step.

## Lifting analytic pairs in a represented affine test square

`exists_point_of_affine_test_pullback` treats any supplied affine test pullback
square of `f`, without a closedness or monomorphism hypothesis. It requires
separatedness of the target algebraic space. For a point `y′` of the source
analytification and a point `a` of `Spec A`'s analytification with equal images in
`Y`, choose a source affine test chart representing `y′`. Intersect that chart's
map into `X` with the target affine test map. Separatedness supplies a finite-type
affine intersection, whose analytic square is a categorical pullback by
`IsAnalytification.isPullback`. The proved ordinary-point lifting theorem produces
a point `d` with the two prescribed chart projections.

The published `pointHom_map` identifies the pushed source test point with its
composite with `f`. This gives the compatible pair for the algebraic pullback
universal property, which yields a map from the intersection to the supplied
affine source test `Spec C`. Fullness of the actual scheme Yoneda
functor and the affine spectrum comparison express it as an algebra map `γ`.
Its first projection equation, together with naturality of the source point
family, gives the required analytic source image. Its second projection equation
identifies the composite algebra map with the target-chart projection.
`affineAnalytificationLocalizedFunctoriality` converts that equality to the
analytic projection equation. Thus every compatible point pair lifts; uniqueness
of the lift and preservation of topological pullbacks are not asserted.

## Closed images and the final reduction

`IsAnalytification.isClosed_of_chart_preimages` proves that closedness of a set in
`Y` is detected on the étale affine test maps. These maps are jointly surjective
and open by the proved analytic étale open-map theorem. If each preimage is closed,
the images of their open complements give open neighborhoods covering the
complement of the original set.

For a closed source set `S`, pull a closed immersion back along each target affine
test. The square's algebraic equation gives equality of test points via
`pointHom_map` and `pointHom_changeRing`. Compatibility and naturality then give
the analytic commuting square. The point-pair lifting lemma identifies the
preimage of `F(S)` under the target test map with the image of the preimage of `S`
under the affine projection. The latter is closed because
`AffineClosedEmbeddingProperty K` makes that projection a closed embedding. The
chart criterion proves that `F` is a closed map. The previously
proved injectivity for monomorphisms, together with continuity, yields a closed
embedding. The open embedding conclusion uses the unconditional
`isOpenEmbedding_of_isOpenImmersion` theorem in the companion helper module.

## Provenance and scope

This is a derived internal proof from the Library's actual represented pullbacks,
closed immersion and coordinate algebra results, affine localized functoriality,
the affine-test clauses of `IsAnalytification`, and the independently reviewed
ordinary analytic point-lifting construction. It supplies the global descent
argument and retains the precise affine premise needed by that argument. The
original immersion target and its imported declarations are unchanged.
