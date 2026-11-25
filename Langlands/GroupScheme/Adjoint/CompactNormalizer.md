# Compact closures of normalizers in adjoint groups

This is an internal derived consequence of the published
`DenseBoundedNormalizerAdjointStatement` proof and the comparison between
algebraic boundedness and compact closure over a nonarchimedean local field.
It requires no integral model or split torus.

`HasCompactNormalizerClosure H` is the predicate that the closure of the full
normalizer of a subgroup `H` is compact in the supplied group topology.
It is defined for an arbitrary group with a topology.

`IsAdjoint.identityQuotient` identifies an adjoint group with its own
full-centre quotient. Its identity morphism is fppf and has trivial kernel;
the full centre is trivial by adjointness. The published assembly theorem
provides the quotient's universal properties.

`SubgroupFunctor.hasDenseRationalPointFamily_map` sends a specified
Zariski-dense subgroup family through a dominant homomorphism. The image of
the dense union of point images is dense in the target, and lies in the
union of the point images of the mapped subgroup. Surjectivity on field
points is unnecessary.

`isCompact_closure_normalizer_of_adjoint` proves this predicate for an adjoint group over an
arbitrary nonarchimedean local field and an algebraically bounded subgroup
whose specified rational points are Zariski dense. The published normalizer
theorem applied to the identity quotient bounds the whole normalizer.
Smoothness implies finite type, so the published boundedness comparison
makes its closure compact in the canonical rational-point topology.

No conclusion about an integral-point subgroup follows here without
additional hypotheses on the integral model.
