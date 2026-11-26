# Weyl quotients of self-centralizing tori in separated smooth groups

This module constructs the normalizer and Weyl quotient required by
[`SelfCentralizingTorusWeylAffinenessStatement`](SelfCentralizingWeylAffinenessStatement.md),
without assuming that the ambient group is affine over the base. The single
deep input is taken as an explicit hypothesis: the proposition
[`SeparatedTorusNormalizerStatement`](SeparatedNormalizerStatement.md), which
supplies a smooth closed normalizer of a closed relative torus in a smooth
separated quasi-compact group scheme. The module states and proves no
affineness criterion; that is the module
[`SelfCentralizingWeylAffinenessCriterion`](SelfCentralizingWeylAffinenessCriterion.md).

## Main results

`Langlands.GroupScheme.exists_separatedTorusWeylQuotient` assumes
`hNorm : SeparatedTorusNormalizerStatement.{u}`, a scheme `S`, a group scheme
`G` over `S` whose structure morphism is smooth, separated and quasi-compact
(as instances), a commutative group scheme `T` with a homomorphism
`t : T.toGrp ⟶ G` such that `RelativeTorus.IsTorus T.toGrp`,
`IsClosedSubgroup t`, and `(torusCentralizer t).IsRepresentedBy t`. It
produces `N`, `n : N ⟶ G`, `W`, `q : N ⟶ W` and `c : T.toGrp ⟶ N` with:

1. `IsClosedSubgroup n`, `(torusNormalizer t).IsRepresentedBy n`, and
   `Smooth N.X.hom`;
2. `IsSeparated W.X.hom`, `QuasiCompact W.X.hom`, and `Etale W.X.hom`;
3. the underlying scheme morphism of `q` is flat, surjective and locally of
   finite presentation;
4. for every `U : Over S` and `y : U ⟶ N.X`, `y ≫ q.hom.hom = 1` exactly when
   `y ≫ n.hom.hom` lies in `(SubgroupFunctor.range t).carrier U`;
5. `c ≫ n = t`, `IsClosedSubgroup c`, the underlying morphism of `c` is an
   open immersion, and `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range c) q`.

`Langlands.GroupScheme.exists_selfCentralizingTorusWeylQuotient` has the same
hypotheses and returns only items 1–4, written in exactly the order and form of
the existence conjuncts of `SelfCentralizingTorusWeylAffinenessStatement`. It
does not use the residue-fibre or maximality hypotheses of that statement.

The auxiliary namespace `Langlands.GroupScheme.SeparatedTorusWeylQuotient`
contains:

- `mem_torusNormalizer_self`: the tautological point `n.hom.hom` of a
  representing normalizer belongs to `torusNormalizer t`;
- `normalizerFamily`: the automorphism of `T` base-changed to `N.X` chosen by
  `HomScheme.normalizerSourceIso`, with `normalizerFamily_comp` (its composite
  with the base change of `t` is the conjugation family of `t` by `n.hom.hom`)
  and `evaluate_normalizerFamily_comp` (the same after restriction along any
  `a : U ⟶ N.X`);
- `cancel_baseChange_map`: right cancellation by the base change of a
  homomorphism whose underlying morphism is a monomorphism;
- `exists_smooth_quotient`: for smooth `N` with a representing normalizer
  inclusion `n`, and `c : Z ⟶ N` representing the preimage of the centralizer
  with `Z` smooth, a smooth surjective map `q : N.X ⟶ Q` whose fibres on every
  test scheme are exactly the left cosets of the range of `c`;
- `exists_homogeneous_quotient`: if moreover `N` is quasi-compact over `S`
  and `c` is a closed subgroup, a `HomogeneousQuotientFromEmbedding.HomogeneousQuotient c`.

## Proof

**Orbit map.** Since `T` is a relative torus it is smooth and affine over `S`,
so `exists_smooth_universal_of_relativeTorus` applied with target `T` itself
gives a smooth universal family `i` over a scheme `Y` representing the relative
Hom functor from `T` to `T`. No hypothesis on `G` is needed for this. The point
`n.hom.hom` lies in the normalizer, so `normalizerSourceIso` gives an
automorphism of `T` over `N.X` whose composite with `t` is conjugation by
`n.hom.hom`. Its classifying morphism `r : N.X ⟶ Y` is the orbit map.

**Fibres.** For `g h : U ⟶ N.X`, universality and `evaluate_comp` turn
`g ≫ r = h ≫ r` into equality of the restricted automorphism families. By
`evaluate_normalizerFamily_comp` these compose with the base change of `t` to
the conjugation families of `t` by `g ≫ n.hom.hom` and `h ≫ n.hom.hom`, and
`cancel_baseChange_map` shows that the two conditions are equivalent. The
theorem `conjugationFamily_eq_iff` identifies equality of conjugation families
with `(g ≫ n)⁻¹ * (h ≫ n)` lying in `torusCentralizer t`. Since group operations
commute with composition by `n`, this is membership of `g⁻¹ * h` in the
centralizer's preimage, which is the range of `c`.

**Quotient.** The coset relation of `c` is a smooth equivalence relation
(`isEquivalenceRelation`, `hasSmoothProjections`), and `N` is locally of finite
type. `schemeQuotientOfMapKernel` therefore gives a scheme quotient with a
smooth surjective projection and exact coset fibres. It is separated by
`TorusCentralizerQuotient.separated_of_closed_subgroup_quotient`, because `c`
is closed. It is quasi-compact over `S` because `N` is
(`TorusCentralizerQuotient.quasiCompact_of_surjective_comp`). It is locally of
finite presentation by flat surjective descent
(`locallyOfFinitePresentation_of_surjective_flat_comp`). The projection is
quasi-compact. This is `exists_homogeneous_quotient`. The proof follows the
affine construction `TorusCentralizerQuotient.exists_homogeneous_quotient`,
with two changes: the Hom scheme from `T` to `G` is replaced by the one from
`T` to `T`, and affineness of `N` is replaced by quasi-compactness.

**Assembly.** The hypothesis `hNorm` gives `N`, `n`, closed and smooth and
representing the normalizer. Then `N` is quasi-compact over `S`, since `n` is a
closed immersion into the quasi-compact group `G`. The theorem
`relativeTorusCentralizerNormalizerInclusion`, applied to the representing
centralizer `t`, gives `c : T ⟶ N` with `c ≫ n = t`, an open immersion
representing the centralizer's preimage. Since `t` and `n` are closed
immersions, `IsClosedSubgroup.of_comp` makes `c` closed. The range of `c` is
normal because the centralizer is normalized by the normalizer
(`torusCentralizer_isNormalizedBy_torusNormalizer`). `HomogeneousQuotient.groupScheme`
and `groupProjection` give `W` and `q`, with the fppf quotient property by
`groupProjection_isFppfQuotient`. `W` is étale by
`etale_of_open_subgroup_quotient`, because `c` is an open immersion.

The kernel condition is rewritten with the representability equalities of `t`
and `c` and the fppf kernel property, then closed by `mem_range_kernelι_iff`,
as in the proof `smoothAffineTorusWeylQuotient`.

## Provenance

This is a derivation from Library constructions. The source for the existence
of the normalizer and Weyl quotient is SGA 3, Exposé XV, Proposition 7.1(iv)
(registered source `sga3-expose-xv-raynaud-2008`, printed p.282, one-based PDF
p.50 of `Expo15.pdf`): for `H` a smooth subgroup whose fibres are torus
centralizers, `Norm_G(H)` is a closed smooth subgroup and `N/H` is a separated
étale group of finite type. This module does not follow the source's argument:
it realizes the quotient through the coset equivalence relation of the orbit
map into the Hom scheme from `T` to `T`.
