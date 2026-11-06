# Reparametrizing the Levi source of an arbitrary parabolic

This is an internal derived adapter for the proof task on the
unitarizable-constituent step of Renard, Théorème VII.1.3. Its provenance is
the published constructions it combines: `IsClosedSubgroup.iso_comp`,
`IsConnectedReductive.of_iso`, `IsSplitComponent.comp_iso`,
`SubgroupFunctor.range_iso_comp`, `normalizedGeneralizedWeight_congr` and
`isNormalizedJacquetExponent_comp_innerIso_iff`. It asserts no new source
translation.

A represented parabolic comes with a Levi map `l : M ⟶ P` out of a chosen
group scheme `M`. This module replaces `M` by an isomorphic group scheme `M'`
through an isomorphism of group schemes `e : M' ≅ M`. The new Levi map is
`e.hom ≫ l` and the new split component is `a ≫ e.inv`. The parabolic
`p : P ⟶ G`, the radical `r : U ⟶ P`, the split torus `A` and the composite
`a ≫ l ≫ p` stay the same.

## Group-scheme statements

- `subgroupMultiplication_iso_comp` shows that the multiplication morphism
  `L' × U ⟶ P` of `e.hom ≫ l` and `r` is the multiplication morphism of `l`
  and `r` precomposed with `e × id_U`. It holds over any base scheme.
  `isIso_subgroupMultiplication_iso_comp` concludes that the first morphism is
  an isomorphism when the second is.
- `IsRationalLeviSubgroup.iso_comp` shows that `e.hom ≫ l` is a rational Levi
  subgroup when `l` is, with the same unipotent radical. The proof combines
  the published transport of closedness and connected reductivity along an
  isomorphism with the multiplication statement above. Affineness of the map
  is unchanged.
- `ParabolicRootPresentation.leviIsoComp` takes a compatible root
  presentation of `p, l, a` and gives one of `p, e.hom ≫ l, a ≫ e.inv` with the
  same presentation data. The data are the torus `T` with its map
  `i : T ⟶ G`, the cocharacter `ν`, the face `J` and the factor `f : A ⟶ T`.
  Only five compatibility fields involve `l` or `a`:
  - the Levi field is `IsRationalLeviSubgroup.iso_comp`;
  - the split-component field is the published `IsSplitComponent.comp_iso`,
    applied to `e.symm`;
  - the standard-Levi equation and the Levi part of the standard-cocharacter
    realization use `SubgroupFunctor.range_iso_comp`, which says that
    `e.hom ≫ l ≫ p` and `l ≫ p` have the same range functor;
  - the factorization equation `f ≫ i = a ≫ l ≫ p` follows from
    `e.inv ≫ e.hom = 𝟙`.

  The remaining fields are copied unchanged, and the realization keeps the
  same standard cocharacter. The restricted simple roots and
  the positive and nonnegative root-combination cones depend only on the data,
  so `restrictedRoots_leviIsoComp`, `positiveCone_leviIsoComp` and
  `nonnegCone_leviIsoComp` hold by `rfl`.

## Exponent statements

- `pointImage_iso_comp` shows that precomposing with an isomorphism does not
  change the literal image of the map on rational points. Each image point
  `j(y)` equals `(e.hom ≫ j)(e.inv(y))`.
- `isNormalizedJacquetExponent_iso_comp_iff` says that a character `χ` of
  `A(k)` is a normalized Jacquet exponent of `π` along `(p, e.hom ≫ l, r, a ≫ e.inv)`
  if and only if it is one along `(p, l, r, a)`. The representation `π` is
  any smooth representation of `G(k)`. The proof applies the published
  `normalizedGeneralizedWeight_congr`. Its three hypotheses hold here:
  - the radical point images are literally the same;
  - the Levi point images agree by `pointImage_iso_comp`;
  - the split-component point maps agree pointwise, since
    `(a ≫ e.inv) ≫ (e.hom ≫ l) ≫ p = a ≫ l ≫ p`.

  The split-component topology on `A(k)` depends only on `A`.
- `isNormalizedJacquetExponent_comp_innerIso_iso_comp_iff` combines this with
  the published inner-conjugation invariance. It compares exponents along
  `(p ≫ innerIso g, e.hom ≫ l, r, a ≫ e.inv)` with those along `(p, l, r, a)`.

## Use and scope

The intended use is a parabolic `q : Q ⟶ G` whose Levi `L` is conjugate to
`M` in `G`. Given `g` in `G(k)` and an isomorphism `e : M ≅ L` with
`e.hom ≫ lQ ≫ q ≫ innerIso g = l ≫ p`, the transported presentation is
`(pres.compAmbientIso (G.innerIso g)).leviIsoComp e`. Its positive cone is the
cone of `pres`, by `positiveCone_leviIsoComp` and the published
`positiveCone_compAmbientIso`. So exponents and cones along `q` become exponents
and cones along a parabolic whose Levi source is `M` itself.

The field is arbitrary for the group-scheme statements. The ambient group is
affine, and local finite type is assumed only for the cone statements. The
exponent statements also take a Hausdorff topology on `k` and a locally compact
nonarchimedean topology on `G(k)`. Field universe `u` and carrier universe `v`
are independent. The module does not show that such `g` and `e` exist, and it
proves no statement about Jacquet support.
