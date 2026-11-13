# The opposite dynamic open cell over an arbitrary base scheme: proof

Workers 3483 and 312.

This module proves
`Langlands.GroupScheme.DynamicBaseOppositeCellStatement.{u}` by the theorem
`Langlands.GroupScheme.dynamicBaseOppositeCell.{u}`. The target and all its
dependencies are unchanged. The base scheme is arbitrary, and the supplied
representatives concern the actual orbit-extension functors on all test schemes,
including nonreduced ones.

## Proof route

The original assertion is Conrad, *Reductive group schemes* (2014),
Theorem 4.1.7(4), pp.112–113, extended to arbitrary base schemes after
Example 4.1.9, p.114; and Conrad–Gabber–Prasad, *Pseudo-reductive groups*,
second edition (2015), Proposition 2.1.8(3), printed p.53/PDF p.79.
The unchanged statement Markdown records the exact source fingerprints and
correspondence. This proof assembles published results by a fibrewise route.

First, the ring theorem `dynamicSmooth_ring` gives smoothness of actual
parabolic and unipotent representatives after base change to each affine
chart of the base. The dynamic functors commute with base change, and
`SubgroupFunctor.IsRepresentedBy.baseChange` transports the representing
homomorphisms. Smoothness is local on the target, so it follows over the
original base. This is implemented by `smooth_of_affine_baseChange` and
`smooth_representatives`. It needs no connectedness.

For any morphism `b : Spec K → S` with `K` a field, the same transport gives
representatives of the dynamic subgroups of the base-changed cocharacter.
`Dynamic.baseChangeCocharacter_powerHom` with exponent `-1` identifies the
opposite cocharacter after base change. Smoothness and affineness of the
ambient group survive base change, so the published smooth-field theorem
`oppositeCellStatement` applies.

The lemma `baseChange_cellMultiplication` identifies base change of the
ordered multiplication with the product-comparison isomorphism followed by
the ordered multiplication of the base-changed representatives. The proof
uses `Functor.map_mul`, functoriality of composition and the two projection
identities of `CartesianMonoidalCategory.prodComparison`. Thus it preserves
both the actual scheme morphism and its order of factors. The product
comparison is an isomorphism because `Over.pullback b` preserves finite
products. Open immersion is invariant under its precomposition. This proves
`isOpenImmersion_field_baseChange`.

Finally, `U ×_S P` is smooth over `S` by `smooth_tensor`, so it is flat and
locally of finite presentation. The ambient group is locally of finite type
over `S` because it is smooth. For every point `s` of `S`, the preceding
field result supplies open immersion after the actual residue-field base
change `S.fromSpecResidueField s`. The published theorem
`Langlands.AlgebraicGeometry.isOpenImmersion_of_fiberwise` concludes that
the original ordered multiplication is an open immersion. Its proof
supplies the required flatness and monomorphism, so these are not additional
hypotheses here.

## Dependencies and scope

The proof imports only current Library modules. In particular, it uses the
published smooth-field opposite cell, not the separate draft of the field
theorem without smoothness, and does not depend on publication of
`dynamicBaseSmoothConnected`.

The main published inputs are:

- `oppositeCellStatement`, module
  `Langlands.GroupScheme.Absolute.OppositeCellProof`;
- `dynamicSmooth_ring`, module
  `Langlands.GroupScheme.Dynamic.SmoothOverRing`;
- `Dynamic.baseChangeCocharacter_powerHom`, module
  `Langlands.GroupScheme.Dynamic.OppositeBaseChange`;
- `SubgroupFunctor.IsRepresentedBy.baseChange`, module
  `Langlands.GroupScheme.SubgroupBaseChange`;
- `smooth_tensor`, module `Langlands.GroupScheme.SmoothProducts`;
- `Langlands.AlgebraicGeometry.isOpenImmersion_of_fiberwise`, module
  `Langlands.AlgebraicGeometry.FiberwiseOpenImmersion`.

No reductivity, connectedness, splitness, Noetherian condition, reducedness,
or affineness of the base scheme is added. Smoothness and relative
affineness of the ambient group remain the hypotheses of the target.
