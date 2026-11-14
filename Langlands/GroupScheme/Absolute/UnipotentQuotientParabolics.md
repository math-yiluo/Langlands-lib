# Geometric parabolic correspondence through a smooth connected unipotent kernel

This is an internal composition of existing group-scheme results, with no
claim to a new original-literature formalization.

Let `k : Type u` be any field, let `G` be a smooth connected affine
`k`-group scheme, let `Q` be an affine `k`-group scheme, and let
`q : G ⟶ Q` be a supplied flat, surjective homomorphism locally of finite
presentation. Assume `HasSmoothConnectedUnipotentKernel q`: the actual
scheme-theoretic kernel of `q` is smooth, connected and unipotent.
Neither perfectness nor reductivity nor a characteristic restriction is
assumed.

Here `IsParabolicSubgroup i` is the existing geometric predicate: `i` is a
closed immersion with smooth source, and after extension to the algebraic
closure it contains an actual Borel subgroup. A Borel witness consists of
an embedding and a homomorphism factoring it through the base-changed
parabolic. The predicate does not assume that a Borel exists over `k`.

`UnipotentQuotientParabolicCorrespondenceStatement` asserts:

1. Every geometric parabolic `i : P ⟶ G` has an actual geometric parabolic
   image `j : I ⟶ Q` and a flat, surjective, quasi-compact homomorphism
   `p : P ⟶ I` locally of finite presentation, with `i ≫ q = p ≫ j`.
   The full inverse-image subgroup functor of `j` is exactly `range i`,
   and the square of the underlying morphisms over `Spec k` is cartesian.
2. For any two closed subgroup embeddings `i : H ⟶ G` and `j : P ⟶ Q`
   with `range i = (range j).comap q`, `i` is geometric parabolic if and
   only if `j` is geometric parabolic.

Ranges, comaps and their equalities are evaluated on every scheme over
`Spec k`, including nonreduced tests.
`unipotentQuotientParabolicCorrespondence` proves exactly this proposition
in arbitrary universe `u`. The helper `isParabolicSubgroup_preimage`
also proves parabolicity of the actual scheme-theoretic inverse image
`SubgroupPreimage.inclusion q j` of any target parabolic.

For image construction, `kernel_le_parabolic` first places the full
actual kernel in every source parabolic by
`IsParabolicSubgroup.normalUnipotent_le`. Closedness and normality of the
kernel inclusion are existing kernel properties. Given an fpqc closed
image factorization, `SubgroupFunctor.comap_range_eq_of_fpqc_square`
then identifies the full inverse image. Representability makes the
square cartesian. The kernel hypothesis makes `q` smooth, so pullback
makes the image projection smooth. Smooth surjective descent from the
source parabolic proves smoothness of the image.

To prove the image geometrically parabolic, extend to the algebraic
closure and choose the Borel witness of the original parabolic.
`HomImage.exists_image` constructs the image of this Borel inside the
base-changed image group. Composing its closed inclusion with the
base-changed image embedding gives a closed subgroup of the target.
`UnipotentQuotientBorels.isBorelSubgroup_image` proves it Borel.
The constructed inclusion into the base-changed image is the required
factorization witness. For the original-field image itself,
`exists_parabolic_image` applies `HomImage.exists_image` to `i ≫ q`
after deriving smoothness of `Q`. The parabolic source is connected by
`IsParabolicSubgroup.connectedSpace`.

For the inverse image, smoothness follows by pulling back the smooth
homomorphism `q`. Extend to the algebraic closure and choose the target
parabolic's Borel witness. Its actual inverse image is Borel by
`UnipotentQuotientBorels.isBorelSubgroup_preimage`. The identities
`SubgroupFunctor.range_baseChangeHom`,
`SubgroupPreimage.range_inclusion` and
`SubgroupFunctor.comap_baseChange` put its full range inside the
base-changed parabolic preimage. The represented subgroup factorization
theorem supplies the required Borel factorization. The kernel hypothesis
survives scalar extension by
`HasSmoothConnectedUnipotentKernel.baseChange`.

Parabolicity transfers to any other closed representative of the same
full inverse image by `IsParabolicSubgroup.of_range_eq`.
For the converse in the second clause, the exact inverse-image equality
constructs the restriction homomorphism using
`SubgroupFunctor.IsRepresentedBy.restrictionHom`; its commuting square
is cartesian by `isPullback_of_comap_eq`. Pullback of `q` supplies
flatness, surjectivity and quasi-compactness of that restriction.
The already proved parabolic image theorem applies.

The input declarations are supplied by:

- `Langlands.GroupScheme.Absolute.UnipotentQuotientBorels`;
- `Langlands.GroupScheme.Absolute.NormalUnipotentParabolicContainment`;
- `Langlands.GroupScheme.Absolute.ParabolicTransport` and
  `Langlands.GroupScheme.Absolute.Borel`;
- `Langlands.GroupScheme.Rational.ParabolicConnectedConjugacy` and
  `Langlands.GroupScheme.Rational.LeviPreimageUnipotentRadical`;
- `Langlands.GroupScheme.SubgroupFunctor.QuotientPreimage`,
  `Langlands.GroupScheme.SubgroupFunctor.FppfImagePullback`,
  `Langlands.GroupScheme.SubgroupBaseChange` and
  `Langlands.GroupScheme.SubgroupPreimage`;
- `Langlands.GroupScheme.HomImage` and
  `Langlands.GroupScheme.Reductive.UnipotentKernelQuotient`.

This unit supplies geometric parabolic images and full inverse images
for a given quotient and kernel hypothesis. It constructs no integral
model, facet association, residue-torus lift or prescribed-point
apartment. `UnramifiedFixedPointSplitTorusStatement` remains open.
