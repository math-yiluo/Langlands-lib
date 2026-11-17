# The original group as the Weil restriction of the descended factor group

Namespace `Langlands.GroupScheme.WeilChart`. This internal construction is the eighth step of the
proof of `AffineWeilPairSingleChartDescentStatement`. It constructs the isomorphism
`weilIso : G ≅ AffineWeil.groupScheme A B G'`, where `G'` is the descended factor group
`factorGroup` (module `Langlands.GroupScheme.Reductive.WeilChartFactorGroup`).

## Setting

As in `WeilChartFactorGroup`: `e : A' ⊗[A] B ≃ₐ[A'] C`, a chart
`P : G_{A'} ≅ AffineWeil.groupScheme A' C H`, factor rigidity `hR`, `H` reductive with almost
simple geometric fibres, `A'` faithfully flat over `A`, the invariance `hinv`, and `G` affine. For
the Weil restriction, `B` is finite and projective over `A`, and `G'` is assumed affine and
locally of finite type. These are instance arguments, supplied in the final assembly by
`factorGroup_isAffine` and `factorGroup_locallyOfFiniteType`.

## Base change of test algebras

- `baseTensor B T` is `B ⊗[A] T` as a `B`-algebra. `inclT B T : T ⟶ B ⊗[A] T` is `t ↦ 1 ⊗ t`,
  with the `A`-structure of `B ⊗[A] T` restricted from `B`. `baseTensorMap χ` is the functoriality
  in `T`, and `inclT_comp_baseTensorMap` holds.
- `chartPush χ f` is the chart map `χ ∘ f`. It is a separate definition so that the algebra
  structures are taken from the objects. On `B ⊗[A] T` the restricted and the canonical
  `A`-structures agree only propositionally.

## Two algebraic facts

- `bijective_of_tmul`: a ring map `κ : C ⊗[A'] T → B ⊗[A] T` with
  `κ (e (a ⊗ b) ⊗ t) = b ⊗ a t` is bijective. The inverse `b ⊗ t ↦ e (1 ⊗ b) ⊗ t` is built
  with `Algebra.TensorProduct.productMap`, and both composites are checked on pure tensors.
- `affinePointMap_bijective`: a bijective map of algebras induces a bijection on points of a
  group scheme.

## The point maps

- `factorEndApp_idem` and `factorEndApp_naturality`: the factor endomorphism on points of `G_B` is
  idempotent and natural.
- `pointsMap T : G(T) →* G'(B ⊗[A] T)` extends coefficients along `inclT` and projects to the
  diagonal factor. The image is fixed, so it is a point of `G'` (`factorPointsEquiv_pointsMap`).
  `pointsMap_naturality` gives naturality in `T`.
- `weilMap T : G(T) →* R_{B/A}(G')(T)` composes `pointsMap` with the inverse of
  `AffineWeil.pointsEquiv` (`pointsEquiv_weilMap`, `weilMap_naturality`).

## Bijectivity

- Chart description of `G'`: `fixedEqLocusEquiv`, `descProj_eqLocus_eq` and `factorChartEquiv X g`.
  The last identifies `G'(X)` with the points of `H` over `X` as a `C`-algebra, for a `B`-algebra
  `X` with a chart map `g`. It composes `factorPointsEquiv`, the point comparison of `G_B` with `G`,
  the chart formula `descProj_eq_diagProj` and `chartFixedEquiv`.
- `factorChartEquiv_pointsMap` and `underPointsEquiv_inclT` (naturality of the chart points along
  `inclChart B f`, the inclusion `T → B ⊗[A] T` as a map of `A'`-algebras). Together they show that
  through these identifications `pointsMap T` becomes the map of points of `H` induced by
  `κ = chartMu ∘ (C ⊗ inclChart)`, with `κ (e (a ⊗ b) ⊗ t) = b ⊗ f(a) t`.
- `pointsMap_bijective_of_chart` and `weilMap_bijective_of_chart` (**chart case**): if `T` has a
  chart map `f : A' → T`, the point maps over `T` are bijective, by `bijective_of_tmul` and
  `affinePointMap_bijective`.
- `weilMap_injective` and `weilMap_surjective` (**general case**). The cover `T → T ⊗[A] A'` is
  faithfully flat and `T ⊗[A] A'` has a chart map. Injectivity follows from the chart case and
  injectivity of points along the cover. For surjectivity, a point over `T` is extended to
  `T ⊗[A] A'` and lifted there. The lift satisfies the descent condition by injectivity over
  arbitrary test algebras, so it descends by `AffinePointDescent.exists_affinePointMap_eq`.
- `weilEquiv T`, `weilIsoNat` (natural isomorphism of the point functors) and `weilIso`
  (**`G ≅ R_{B/A}(G')`**), reconstructed by the Library's `AffinePointComparison.iso`.

## Provenance

This is internal. In Conrad, *Reductive group schemes* (2014), proof of Proposition 6.4.4, the
isomorphism `G ≅ R_{B/A}(G')` is obtained by descending the given isomorphism over the étale
cover. Here the comparison map is defined directly from the diagonal factor projection. It is
bijective over the cover by the chart description, and hence everywhere by faithfully flat descent
of points.
