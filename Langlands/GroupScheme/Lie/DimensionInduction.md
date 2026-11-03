# Induction on the dimension of the actual Lie kernel

Author: Worker 1446.

This internal derived module provides an induction parameter for smooth connected
actual affine group schemes over any field, in arbitrary universe and
characteristic. It uses the published dual-number identity kernel without
replacing that kernel by a chosen vector space.

`Lie.dimension G` is `Module.finrank k (Additive (lieKernel G k))`. For smooth
affine groups the imported `Lie.finiteDimensional_lieKernel` ensures that this
natural number is the dimension of a finite-dimensional vector space. The
definition itself needs only affineness; the following results retain smoothness.

`Lie.isIso_of_surjective_targetMapLinear` strengthens the published
`lieSubgroupEquality` conclusion to an isomorphism. The ambient group is smooth,
affine and connected, and the closed subgroup is smooth and affine. Surjectivity
of the actual linear tangent map supplies exactly the dual-number point lifts
required by `lieSubgroupEquality`. That theorem makes the subgroup range the top
subgroup functor on every test scheme. The represented-subgroup comparison with
the identity embedding then produces an isomorphism whose homomorphism is the
original closed inclusion.

`Lie.dimension_lt_of_proper_closedSubgroup` gives strict dimension decrease
for every nonisomorphic smooth closed inclusion into such a connected ambient
group. The subgroup need not be connected. A closed inclusion is monomorphic,
so its actual tangent map is injective. Finite-dimensional linear algebra gives
the dimension inequality. Equality would make this same map a linear equivalence,
hence surjective, contradicting the preceding isomorphism result.

`smoothConnectedAffineGroup_lieDimension_induction` is natural-number strong
induction on this dimension. At each group its hypothesis covers every smooth
connected affine group over the same field with smaller Lie dimension. Thus the
hypothesis can be applied to a proper connected smooth closed subgroup using the
preceding lemma, or to a quotient after a separate dimension decrease proof.
This module does not construct quotients or assert their dimension decrease.

The provenance is internal: the arguments compose the published actual Lie
kernel maps, their finite-dimensionality, the already proved
`LieSubgroupEqualityStatement`, represented-subgroup comparison, and ordinary
finite-dimensional linear algebra. The module neither proves nor assumes the
Borel normalizer theorem; the structural steps needed for that theorem remain
separate obligations.
