# Closed representability of normalizers and centralizers of closed subgroups

This module shows that the all-test subgroup functors `(range i).normalizer` and `(range i).centralizer` (from `Rational.TorusNormalizer`) have closed representatives for every closed subgroup `i : H ⟶ G` of an affine group scheme `G` over a field. They are represented on every test scheme over the base, affine or not, by explicit closed subgroup schemes cut out by ideals of a coordinate algebra.

## Corepresented groups

Let `R` be a commutative ring and `Spec B` the corepresented group scheme `groupScheme F e`.

- `isAffineCutOutBy_of_isCutOutBy`: suppose the subgroups `affineSubgroups K A`, given by the points of a subgroup functor `K` over `Spec A` with its canonical structure map, are cut out by an ideal `J`. Then `K` is cut out by `J` on every affine test `Spec A ⟶ Spec R`, in the sense of the published `IsAffineCutOutBy`. The proof identifies `Over.mk f` with the spectrum of `A`, made an `R`-algebra through `f`. Membership in `K` is transported along this isomorphism, and the classifying ring map of a point is compared with `pointRing`.
- `exists_ideal_range`: for a group-scheme homomorphism `j : K ⟶ Spec B` whose underlying morphism is a closed immersion, there is an ideal `I` of `B` such that, on every test scheme `U`, a point lies in `range j` exactly when its classifying map `B ⟶ Γ(U)` kills `I`. The proof writes `j` as `Spec (B ⧸ I) ⟶ Spec B` up to isomorphism (Mathlib's `IsClosedImmersion.Spec_iff`). It then uses the published factorization criterion `factorsThrough_affineQuotient_iff` for arbitrary test schemes.
- Given such an `I` (hypothesis `hI`), `isAffineCutOutBy_range` and `isCutOutBy_range` show that `range j` is cut out by `I`. `mem_range_iff_mem_affineSubgroups` restates membership through the global-section points.
- `pointsEquiv_comp_affinePointsEquiv_symm` computes the points, over an arbitrary test scheme `V`, of the restriction along `a : V ⟶ Spec A` of an `A`-point `g`. They are the image of `g` under the algebra map `A ⟶ Γ(V)` adjoint to `a`.
- `affineSubgroups_normalizer` and `affineSubgroups_centralizer`: over every spectrum of an algebra, the points of the normalizer and of the centralizer of `range j` form the algebra-level `normalizerFamily` and `centralizerFamily` of the points of `range j`. In the forward direction an algebra extension `A ⟶ A'` is realized by the test scheme `Spec A'`. In the reverse direction an arbitrary refinement `V ⟶ Spec A` is turned into the algebra map `A ⟶ Γ(V)`, using the all-test description of `range j`.
- `isCutOutBy_affineSubgroups_normalizer` and `isCutOutBy_affineSubgroups_centralizer`: assuming `B ⧸ I` is projective over `R`, these families are cut out by `subgroupNormalizerIdeal e I` and `subgroupCentralizerIdeal e I` from `CorepresentedNormalizer`.
- `isRepresentedBy_normalizer` and `isRepresentedBy_centralizer`: the closed immersions `cutHom` of `Spec (B ⧸ subgroupNormalizerIdeal e I)` and `Spec (B ⧸ subgroupCentralizerIdeal e I)` represent the normalizer and the centralizer of `range j` on every test scheme. This is the published affine-to-all-tests reduction `isRepresentedBy_cutHom_affineSubgroups`, which covers a nonaffine test by affine opens.

## Transport along isomorphisms

- `SubgroupFunctor.normalizer_range_le_comap` and `centralizer_range_le_comap`: a homomorphism `f : G ⟶ G'` maps the normalizer (centralizer) of `range i` into the normalizer (centralizer) of `range (i ≫ f)`. This holds because composition with `f` is a group homomorphism on points.
- `normalizer_range_eq_comap_of_iso` and `centralizer_range_eq_comap_of_iso`: these are equalities when `f` is an isomorphism.

## Affine groups

For an affine group scheme `G` over `Spec R`, `AffineCoordinates.coordinateHom i` is `i` followed by the inverse of the published `AffineCoordinates.groupSchemeIso G`. It is a closed immersion when `i` is. Given an ideal `I` describing its range as above, with `B ⧸ I` projective:

- `AffineCoordinates.isRepresentedBy_normalizer_range` and `isRepresentedBy_centralizer_range`: `(range i).normalizer` and `(range i).centralizer` are represented on every test scheme by the corresponding `cutHom` followed by `groupSchemeIso G`. The proofs combine the transport lemmas with the published `IsRepresentedBy.comp_iso`.
- `isClosedSubgroup_normalizer_range` and `isClosedSubgroup_centralizer_range`: these representatives are closed subgroups.

The final theorem `hasClosedRepresentative_normalizer_centralizer_range` works over a field `k`. For every affine group scheme `G` over `Spec k` and every closed subgroup `i : H ⟶ G`, both `(range i).normalizer` and `(range i).centralizer` satisfy `HasClosedRepresentative`. Projectivity of `B ⧸ I` is automatic over a field. Neither `G` nor `H` needs to be of finite type, smooth or reduced. For a torus homomorphism, `torusNormalizer i` is `(range i).normalizer` by definition and `torusCentralizer i = (range i).centralizer` (`torusCentralizer_eq_centralizer_range`).

## Provenance

This is an internal construction toward task `0f453442`. The field statement is the representability part of Milne, *Algebraic Groups* (2017), Propositions 1.83 and 1.92 (printed pp. 31 and 33, PDF pp. 47 and 49). It is proved here for affine group schemes, not necessarily of finite type, and their closed subgroups, for the functors tested on all schemes over the base. Milne's algebraic groups are of finite type but need not be affine, so neither statement contains the other. Uniqueness of the representative is not stated. The proof route is described in `CorepresentedNormalizer` and above; it does not follow Milne's transporter argument (Proposition 1.79). Smoothness of the representatives, needed for split tori, is not addressed in this module.
