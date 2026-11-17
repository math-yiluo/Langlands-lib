# Fppf quotients on subgroup preimages

Worker 324, with interface input from Worker 5698.

This module supplies derived geometry for the inverse image of a subgroup under
an fppf quotient. It works over every scheme `S : Scheme.{u}` and in every
universe `u`. It does not prove that an extension is of multiplicative type.

## Provenance and imports

This is an internal categorical derivation from the published Library APIs,
rather than a translation of an additional result from the literature. It
imports:

- [`SubgroupPreimageKernel`](SubgroupPreimageKernel.md), for the comparison of
  the full kernels of a quotient and its inverse-image projection; this also
  imports the actual group-scheme pullback, its range, and its geometric
  properties from
  [`Reductive.UnipotentRadicalQuotientReduction`](Reductive/UnipotentRadicalQuotientReduction.md);
- [`Rational.LeviFactorization`](Rational/LeviFactorization.md), for
  `IsClosedSubgroup.of_comp` and `IsCentral.of_comp`.

The uniqueness comparison for representatives is
`SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy`. Morphism properties of
the pullback projection follow from stability under base change. All results
below are implemented and proved in the paired Lean file.

## Actual inverse image and arbitrary representatives

Let `q : G ⟶ Q` and `j : K ⟶ Q` be homomorphisms of group schemes over `S`.
The existing `SubgroupPreimage.groupScheme q j` is the pullback, with
`inclusion q j` to `G` and `projection q j` to `K`. All declaration names in
this section are in `Langlands.GroupScheme.SubgroupPreimage`.

`locallyOfFinitePresentation_projection` proves that the projection is locally
of finite presentation whenever the underlying morphism of `q` is. With
`Mono j.hom.hom`, `isRepresentedBy_inclusion` proves that the inclusion
represents `(SubgroupFunctor.range j).comap q`, using the existing pullback
monomorphism and range equality.

Suppose `p : P ⟶ G` is any other representative of this subgroup functor,
witnessed by `hp`, and `Mono j.hom.hom` holds.

- `representedIso q j hp : P ≅ groupScheme q j` compares the representatives.
  `representedIso_hom_comp` says that its homomorphism followed by the actual
  inclusion equals `p`.
- `representedProjection q j hp : P ⟶ K` is this comparison followed by the
  actual projection. `representedProjection_comp` proves
  `representedProjection q j hp ≫ j = p ≫ q`.
- `flat_representedProjection`, `surjective_representedProjection`, and
  `locallyOfFinitePresentation_representedProjection` transfer the respective
  property of the underlying morphism of `q` to this projection. Their proofs
  compose an isomorphism with the actual pullback projection.

For the actual preimage's structure morphism over `S`, `flat` assumes that
`q` is flat and `K` is flat over `S`. Likewise,
`locallyOfFinitePresentation` assumes that `q` and the structure morphism of
`K` are locally of finite presentation. Each conclusion follows by composing
the projection with the structure morphism of `K`.

## The original kernel inside the preimage

In addition, let `h : H ⟶ G` satisfy `Mono h.hom.hom`, and let
`hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range h) q`.
Thus `q` is flat, surjective, and locally of finite presentation, and its full
kernel has range `SubgroupFunctor.range h`.

`quotientKernelIso q j h hq : H ≅ kernel (projection q j)` first identifies
`H` with the full kernel of `q`, by uniqueness of representatives of
`SubgroupFunctor.range h`, and then uses the inverse of the existing
`kernelIso q j`. No monomorphism assumption on `j` is needed for this
construction.

`quotientKernelInclusion q j h hq : H ⟶ groupScheme q j` is this isomorphism
followed by the full kernel inclusion. The module proves:

- `quotientKernelInclusion_mono`: its underlying morphism over `S` is a
  monomorphism.
- `quotientKernelInclusion_comp`: its composite with `inclusion q j` equals
  `h`. The proof combines compatibility of the two kernel comparisons.
- `range_quotientKernelInclusion`: its range equals the range of
  `kernelι (projection q j)`, using invariance of range under an isomorphism
  of the source.
- `isFppfQuotient_projection_of_kernel`: the actual projection is an fppf quotient by
  the range of `quotientKernelInclusion`. The geometric properties follow by
  base change, and exactness is the preceding range equality.
- `isClosedSubgroup_quotientKernelInclusion`: if `h` and `j` are closed
  subgroups, the new kernel inclusion is a closed subgroup. Its composite
  with the closed preimage inclusion is `h`, so the closed-factor lemma
  applies.
- `isCentral_quotientKernelInclusion`: if `j` is a monomorphism and `h` is
  central in `G`, the new kernel inclusion is central in the preimage.
  This uses the same compatibility equation and reflection of centrality
  through the monic preimage inclusion.

The compatibility equations for the representative isomorphism, represented
projection, and kernel inclusion also have generated reassociated forms.
