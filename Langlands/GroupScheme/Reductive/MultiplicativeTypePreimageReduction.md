# Multiplicative-type preimages: reduction to the extension statement

This module gives a conditional reduction for the multiplicative-type part of
the normal-central theorem. It assumes the proposition
`MultiplicativeTypeFpqcExtensionStatement.{u}` and centrality of the actual
preimage inclusion. It does not prove either input or the full
`MultiplicativeTypeNormalCentralStatement`.

## Provenance and imports

The results are derived from the published statement
[`MultiplicativeTypeFpqcExtensionStatement`](../Torus/MultiplicativeTypeFpqcExtensionStatement.md)
and the quotient-preimage and flatness constructions in
[`SubgroupPreimageQuotient`](../SubgroupPreimageQuotient.md) and
[`RelativeMultiplicativeTypeFlat`](../Torus/RelativeMultiplicativeTypeFlat.md).
The commutativity of a central subgroup is the existing
`IsCentral.isCommMonObj` from
[`CentralSubgroupGeometry`](../Rational/CentralSubgroupGeometry.md).
No additional result from the literature is asserted here.

## Hypotheses and conclusions

All declarations are in `Langlands.GroupScheme.SubgroupPreimage`, over an
arbitrary scheme `S : Scheme.{u}`. Let `q : G ⟶ Q`, `j : K ⟶ Q`, and
`h : H ⟶ G` be group-scheme homomorphisms. The hypotheses are:

- `G` is affine over `S`;
- `H` and `K` are locally of finite presentation over `S`, and `K` is affine
  over `S`;
- `hh : IsClosedSubgroup h` and `hj : IsClosedSubgroup j`;
- `hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range h) q`;
- both `H` and `K` satisfy the relative predicate
  `RelativeMultiplicativeType.IsMultiplicativeType`;
- `hC : IsCentral (inclusion q j)`;
- `hExt : MultiplicativeTypeFpqcExtensionStatement.{u}`.

`isMultiplicativeType_of_isCentral_inclusion` concludes that the actual
`groupScheme q j` is of multiplicative type. In particular, this is a
reduction with explicit geometric hypotheses on the two factors, rather
than an unconditional proof of the extension statement.

`isMultiplicativeType_represented_of_isCentral_inclusion` has the same
hypotheses and additionally accepts any `p : P ⟶ G` representing
`(SubgroupFunctor.range j).comap q`. It concludes that `P` is of
multiplicative type.

## Implemented proof

Closedness supplies the monomorphisms of the two subgroup inclusions.
Closedness of `h` and affineness of `G` make `H` affine. The flatness
theorem for relative multiplicative-type groups supplies flatness of `H`
and `K`. Flatness and local finite presentation of `q` come from `hq`.

The actual preimage is affine by closedness of its inclusion in the
affine group `G`. Its flatness and local finite presentation over `S`
follow by composing its pullback projection with the structure morphism
of `K`. The earlier quotient adapter supplies a monomorphism
`quotientKernelInclusion q j h hq` from `H` and proves that
`projection q j` is an fppf quotient with exactly this kernel.

The central inclusion of the preimage is monic, so its source is a
commutative group object by `IsCentral.isCommMonObj`. For each point
`s : S`, Mathlib's `Functor.isCommMonObj_obj` transports commutativity
through `Over.pullback (S.fromSpecResidueField s)`. Hence every actual
residue fibre satisfies the commutative alternative in the second clause
of `hExt S`. Applying that clause gives multiplicative type of the
preimage.

For an arbitrary representative, `representedIso q j hp` identifies it
with the actual preimage. The relative multiplicative-type predicate
transfers across this isomorphism by `IsMultiplicativeType.of_iso`.
