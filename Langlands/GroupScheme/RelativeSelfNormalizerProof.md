# Proof of field-fibre detection of relative self-normalization

`Langlands.GroupScheme.relativeSelfNormalizer` proves the published statement
`Langlands.GroupScheme.RelativeSelfNormalizerStatement.{u}`. Here `S` is a
scheme, `G` is a smooth group over `S` with affine structure map, and
`i : H ⟶ G` is a smooth closed subgroup. Assume that for every field
`k : Type u` and every morphism `Spec k ⟶ S`, the normalizer of the range of
the base change of `i` equals that range. The theorem then concludes that
`(range i).normalizer = range i` over `S`.

The hypothesis that `H` is geometrically connected is not used. The proof
does not represent the normalizer by a subgroup scheme, and it uses no
unproved statement.

## Route

The inclusion `range i ≤ (range i).normalizer` is the Library lemma
`le_normalizer`. For the reverse inclusion, take a test `T` over `S` and a
point `x : T ⟶ G.X` in the normalizer. The proof shows that `x` lies in
`range i` in four steps.

1. **Affine cover of the test** (`SubgroupFunctor.mem_range_of_affineCover`).
   Since `i` is a monomorphism, membership of `x` in `range i` may be checked
   after restricting `x` to each member of the affine open cover of `T.left`.
   The morphism `Sigma.desc` from the disjoint union of that cover to
   `T.left` is flat, surjective and locally of finite presentation. The last
   property comes from `IsZariskiLocalAtSource.sigmaDesc`; the
   `IsZariskiLocalAtSource` instance for `LocallyOfFinitePresentation` is
   supplied explicitly, because instance search does not find it. Mathlib's
   fppf instance in `Mathlib.AlgebraicGeometry.Sites.Fpqc` makes this morphism
   an effective epimorphism. The Library lemma
   `SubgroupFunctor.mem_range_of_comp_mem_range` then descends membership,
   using the glued point `Sigma.desc` of the local preimages. The restriction
   of `x` to each cover member still lies in the normalizer, since subgroup
   functors are stable under pullback of tests.

2. **Affine tests: reduction to an affine base**
   (`SubgroupFunctor.normalizer_carrier_le_of_isAffine`). Let the test `T`
   have affine total space, and let `A = Γ(T.left, ⊤)`. Base change along
   `f = T.left.isoSpec.inv ≫ T.hom : Spec A ⟶ S`. The base-changed groups
   remain smooth, `G` becomes affine because `G.X.hom` is an affine morphism,
   and `i` remains a closed subgroup (`IsClosedSubgroup.baseChange`).
   `normalizer_carrier_le_iff_baseChange` combines the Library results
   `range_baseChangeHom` and `normalizer_baseChange`. It identifies
   self-normalization over `Spec A` on a test with self-normalization over
   `S` on the same test regarded over `S`. `normalizer_carrier_le_of_iso`
   transports the conclusion along the isomorphism between `T` and
   `Spec A` regarded over `S`.

3. **Affine group over an affine base**
   (`SubgroupFunctor.normalizer_carrier_le_of_affine`). Over `Spec R` with
   `G.X.left` affine, the Library isomorphism
   `AffineCoordinates.groupSchemeIso` identifies `G` with the corepresented
   group scheme of its coordinate algebra. That algebra is smooth by
   `AffineCoordinates.smooth_algebra`. `normalizer_carrier_le_iff_of_iso`,
   which uses `mem_range_comp_iso_iff` and the Library lemma
   `normalizer_range_eq_comap_of_iso`, moves the question across this
   isomorphism.

4. **Corepresented case**
   (`Corepresented.normalizer_carrier_le_of_field`). Let `G` be the
   corepresented group scheme of a smooth `R`-algebra `B`, and let
   `j : K ⟶ G` be a smooth closed subgroup.
   - `exists_ideal_range` and `isCutOutBy_range` give an ideal `I` of `B`
     that cuts out the points of `range j`.
   - `range j` is represented both by `j` and by `cutHom`, the inclusion of
     `Spec (B ⧸ I)`. `IsRepresentedBy.isoOfIsRepresentedBy` therefore gives
     an isomorphism of `K` with `cutGroupScheme`. So `Spec (B ⧸ I)` is smooth,
     and by `smooth_groupScheme_iff`, `B ⧸ I` is a smooth `R`-algebra, hence
     flat and formally smooth.
   - `B` is finitely presented because it is smooth, so `I` is finitely
     generated (`Algebra.FinitePresentation.ker_fG_of_surjective`).
   - `affineSubgroups_normalizer` translates the scheme-level normalizer on
     spectra of `R`-algebras into the algebra-level `normalizerFamily`.
     `Corepresented.normalizerFamily_le_of_field` from
     `Langlands/GroupScheme/RelativeSelfNormalizer/SquareZero.lean` then
     concludes. Its field hypothesis is the normalizer inclusion on
     `R`-algebras `E` whose structure map factors through a field.

**Field hypothesis.** `SubgroupFunctor.normalizer_carrier_le_of_fieldPoint`
turns the hypothesis of the statement into the inclusion of the normalizer in
`range i` on every test over `S` whose structure map factors through some
`Spec k ⟶ S` (again by `normalizer_carrier_le_iff_baseChange`). In step 2,
consider an `A`-algebra `E` whose structure map factors as `A → k → E`
through a field. The test `Spec E ⟶ Spec A ⟶ S` is then isomorphic over `S`
to the test `Spec E ⟶ Spec k ⟶ S`, where `Spec k ⟶ S` is
`Spec k ⟶ Spec A ⟶ S`. The isomorphism is `Over.isoMk` of the identity and
uses `Spec.map` of the factorization. This supplies the field hypothesis of
step 3.

## Helper declarations

All of the following are in `Langlands.GroupScheme.SubgroupFunctor`:

- `normalizer_carrier_le_of_iso`
- `comp_inv_hom_comp_hom`
- `mem_range_comp_iso_iff`
- `normalizer_carrier_le_iff_of_iso`
- `normalizer_carrier_le_iff_baseChange`
- `normalizer_carrier_le_of_fieldPoint`
- `mem_range_of_affineCover`
- `normalizer_carrier_le_of_affine`
- `normalizer_carrier_le_of_isAffine`

The corepresented step is
`Langlands.GroupScheme.Corepresented.normalizer_carrier_le_of_field`. The
algebraic core and its proof are described in
`Langlands/GroupScheme/RelativeSelfNormalizer/SquareZero.md`.

## Relation to the literature

The target statement cites Brian Conrad, *Reductive group schemes* (2014),
Proposition 2.1.6 and Lemma B.3.1 (source
`conrad-2014-reductive-group-schemes`). Conrad represents the normalizer by a
finitely presented closed subgroup scheme and proves that `H` maps
isomorphically onto it by a fibrewise isomorphism criterion. This proof takes
a different route. It reduces to affine tests over an affine base and argues
directly with a normalizing point. Formal smoothness and flatness of
`B ⧸ I`, field-valued tests built from square-zero thickenings, and
Nakayama's lemma show that the point already lies in `H`.
