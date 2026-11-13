# Borel correspondence through a smooth connected unipotent kernel

This is an internal composition of published Library results, with no claim
to a new original-literature formalization.

Let `k : Type u` be an algebraically closed field, let `G` be a smooth connected
affine `k`-group scheme, let `Q` be an affine `k`-group scheme, and let
`q : G ⟶ Q` be a supplied flat, surjective homomorphism locally of finite
presentation. Assume `HasSmoothConnectedUnipotentKernel q`: the actual
scheme-theoretic kernel of `q` is smooth, connected and unipotent.
No reductivity, torus splitting or characteristic restriction is assumed.
Smoothness and connectedness of `Q` are derived.

`UnipotentQuotientBorelCorrespondenceStatement` asserts two facts:

1. Every Borel embedding `i : B ⟶ G` has an actual Borel image `j : I ⟶ Q`
   with a flat, surjective, quasi-compact map `p : B ⟶ I` locally of finite
   presentation, satisfying `i ≫ q = p ≫ j`. Its full inverse image equals
   `range i` on every relative scheme test, and the square of the underlying
   morphisms over `Spec k` is cartesian.
2. If `j : B ⟶ Q` is Borel and `i : P ⟶ G` is any closed representative of
   its full inverse-image subgroup functor, then `i` is Borel.

`unipotentQuotientBorelCorrespondence` proves exactly this proposition in
arbitrary universe `u`. The helper `isBorelSubgroup_preimage` specializes the
second clause to the actual `SubgroupPreimage.inclusion q j`.

The implemented proof begins with `kernel_le_borel`. The published
`normalUnipotentBorelContainment` applies to the actual closed kernel:
its range is normal by `HopfPrimitive.isNormal_range_kernelι`. Consequently
every source Borel contains the full kernel, including on nonreduced tests.

For a supplied fpqc image factorization, `isBorelSubgroup_image` uses
`SubgroupFunctor.comap_range_eq_of_fpqc_square` and this kernel containment
to identify the inverse-image functor. Representability gives the cartesian
square. The actual smooth kernel makes `q` smooth, and its connectedness
gives geometrically connected fibres. Pullback makes `p` smooth. The published
`isBorelSubgroup_of_quotient_square` then proves that the image is Borel.
`exists_borel_image` constructs the factorization using
`HomImage.exists_image`; it first derives smoothness of `Q` by smooth
surjective descent from `G`.

For inverse images, `isBorelSubgroup_of_range_eq_comap` chooses a Borel
`i₁ : B₁ ⟶ G` by `BorelExistence.exists_isBorelSubgroup`, constructs its Borel
image, and applies the published `borelConjugacy` theorem in `Q`.
`rationalPointLift` lifts the conjugating rational point to `G`.
The conjugate of `i₁` is Borel and, by `kernel_le_borel`, still contains
the full kernel. The conjugated factorization is an actual fppf image;
`SubgroupFunctor.IsFppfImage.comap_eq_of_kernel_le` identifies its full
inverse image. Finally `IsClosedSubgroup.sourceIsoOfRangeEq` identifies
the supplied closed representative with this conjugate Borel, and Borel
transport along this source isomorphism proves the conclusion.
This follows the conjugacy-and-lift route of the published central-isogeny
Borel-preimage proof, using normal unipotent containment to handle the kernel.
That central-isogeny module is not imported.

The actual published inputs are provided by:

- `Langlands.GroupScheme.Absolute.NormalUnipotentBorelContainmentProof`;
- `Langlands.GroupScheme.Absolute.BorelQuotientDescent`;
- `Langlands.GroupScheme.Absolute.BorelConjugacyProof` and
  `Langlands.GroupScheme.Absolute.BorelExistence`;
- `Langlands.GroupScheme.Reductive.UnipotentKernelQuotient`;
- `Langlands.GroupScheme.SubgroupFunctor.QuotientPreimage`,
  `Langlands.GroupScheme.HopfPrimitiveQuotient` and
  `Langlands.GroupScheme.ConjugacyBaseChange`;
- `Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction`
  and `Langlands.GroupScheme.ClosedSubgroupMonomorphism`.

This unit supplies algebraic Borel correspondence for a given quotient.
It constructs no integral model, facet association, residue-torus lift or
prescribed-point apartment. `UnramifiedFixedPointSplitTorusStatement`
remains open.
