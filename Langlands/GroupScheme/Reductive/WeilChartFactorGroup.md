# The descended factor group `G'` over the descended coefficient algebra

Namespace `Langlands.GroupScheme.WeilChart`. This internal construction is the sixth step of the
proof of `AffineWeilPairSingleChartDescentStatement`. It turns the descended diagonal factor
projection `descProj` (module `Langlands.GroupScheme.Reductive.WeilChartFactorDescent`) into an
endomorphism of the group scheme `G_B = G ×_{Spec A} Spec B`. The candidate `G'` over `Spec B` is
then the closed subgroup of `G_B` fixed by this endomorphism.

## Algebras over `B`

- `resB A X` is a `B`-algebra `X` regarded as an `A`-algebra through `A → B`.
  `structB X : B →ₐ[A] X` is its structure map, and `resBHom χ` is a map of `B`-algebras
  regarded as a map of `A`-algebras. `resBHom_comp_structB` relates them.
- `bPointsEquiv G X` identifies the points of `G_B` over `X` with the points of `G` over
  `resB A X`. It is the inverse of the Library's `affinePointsBaseChangeMulEquiv`.
  `bPointsEquiv_symm_naturality` records its naturality.

## The factor endomorphism and the factor group

The setting is that of `WeilChartFactorDescent`: `e`, `P`, `hR`, `hred`, `hsimple`, `A'`
faithfully flat over `A`, and the invariance `hinv`. In addition `G` is affine.

- `factorEndApp X` transports `descProj (structB X)` to the points of `G_B` over `X`.
  `factorEndNat` is the resulting endomorphism of the point functor of `G_B`. Naturality follows
  from `descProj_map` and `resBHom_comp_structB`.
- `isAffine_baseChange_left`: `G_B` is affine.
- `factorEnd : G_B ⟶ G_B` is the group-scheme endomorphism reconstructed from `factorEndNat` by
  the Library's `AffinePointComparison.map`. `factorEnd_points` gives its action on points.
- `exists_factorGroup`: the subgroup functor of points fixed by `factorEnd`
  (`endomorphismFixedSubgroup`) is represented by a closed subgroup. This is the Library's
  `endomorphismFixedSubgroup_isClosedRepresentable`, which applies because `G_B` is affine and
  hence separated.
- `factorGroup` (the group `G'`) and `factorIncl : G' ⟶ G_B` are a chosen such representative.
  `factorIncl_spec` records the representation and that the inclusion is a closed immersion.
- `factorGroup_isAffine`: `G'` is affine, as a closed subscheme of an affine scheme.
  `factorGroup_locallyOfFiniteType`: if `G` is locally of finite type over `Spec A`, then `G'` is
  locally of finite type over `Spec B`. The inclusion is a closed immersion, and `G_B → Spec B`
  is a base change of `G → Spec A`.
- `factorIncl_injective` and `mem_range_factorIncl_iff`: on points over a `B`-algebra `X`,
  composition with the inclusion is injective. Its image consists of the points fixed by
  `factorEndApp X`.
- `fixedPoints X` is that subgroup of fixed points. `factorPointsEquiv X : G'(X) ≃* fixedPoints X`
  is composition with the inclusion (`factorPointsEquiv_apply`). It is natural in `X`
  (`factorPointsEquiv_naturality`).

## Provenance

This is internal. In Conrad, *Reductive group schemes* (2014), proof of Proposition 6.4.4, the
group `G'` over `B` is obtained by descent. Here it is constructed as the fixed subgroup of the
diagonal factor projection of `G_B`. This uses only the Library's reconstruction of
homomorphisms from affine points and its closed fixed subgroups. The identification
`G ≅ R_{B/A}(G')` and the properties of `G'` are proved in later modules.
