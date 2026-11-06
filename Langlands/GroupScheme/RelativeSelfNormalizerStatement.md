# Detecting self-normalization on field fibres

`Langlands.GroupScheme.RelativeSelfNormalizerStatement.{u}` concerns actual
group schemes over every `S : Scheme.{u}`. Let `G` be smooth and affine over
`S`, and let `i : H ⟶ G` be a smooth closed subgroup with geometrically connected
fibres. Suppose that for every field `k : Type u` and every actual morphism
`b : Spec k ⟶ S`, the normalizer of the range of the base-changed homomorphism
`i_k` equals that range. The conclusion is
`(SubgroupFunctor.range i).normalizer = SubgroupFunctor.range i` over `S`.

Both the hypotheses and the conclusion are equalities of subgroup functors
on every test scheme over their respective bases. In particular, the
hypothesis is stronger than an equality of groups of field-rational points;
the conclusion includes tests with nilpotents. No Noetherian, reduced-base,
field-perfection, splitness or connectedness hypothesis on `G` is imposed.
This is field-fibre detection, not descent along the disjoint union of the
field-valued points: that map need not be flat.

The statement is derived from Brian Conrad, *Reductive group schemes* (2014),
Proposition 2.1.6 (printed and one-based PDF pp.61–62) and Lemma B.3.1
(printed and one-based PDF p.288). The proof of Corollary 5.2.8 on p.156
explicitly uses this combination for parabolic subgroups. The registered
source is `conrad-2014-reductive-group-schemes`, SHA256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The general smooth-subgroup formulation here is a derived consequence,
rather than a verbatim parabolic assertion of that corollary.

The intended argument represents the normalizer by a finitely presented
closed subgroup `N`, factors `H ⟶ G` through `N`, and proves that `H ⟶ N`
is an isomorphism. Normalizers commute with arbitrary base change, and the
field-fibre hypotheses make each field base change of this factor an
isomorphism. Lemma B.3.1 applies to morphisms between schemes locally of
finite presentation over `S` when the source is flat; smoothness supplies
flatness of `H`. Flatness of `N` is not a premise. These representability,
factorization and fibrewise-isomorphism steps remain proof obligations.

This module defines a proposition only and claims no proof.
