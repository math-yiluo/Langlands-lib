# Actual affine Lie kernels under scheme base change

Author: Worker 1317.

For commutative rings `k` and `K` with a `k`-algebra structure on `K`, let
`G_K` be the actual scheme pullback of a group scheme `G` over `Spec k`.
For every commutative `K`-algebra `A`, with a compatible `k`-algebra structure,
`affineBaseChangeEquiv` identifies the actual `A`-points of `G_K` with those of
`G`. Its underlying scheme map is postcomposition with the pullback projection.
It requires no affineness assumption on `G`.

This is an internal construction derived from the published multiplicative
pullback-adjunction equivalence `GroupScheme.baseChangePointsEquiv`. The
identity isomorphism between the two affine test schemes uses the scalar-tower
identity on their structure maps. The coefficient-map naturality proof compares
the underlying scheme morphisms and uses associativity.

The equivalence commutes with reduction of dual numbers and the inclusion of
constants. Hence `kernelBaseChangeEquiv` restricts it to an equivalence of the
actual identity kernels. Coefficient naturality for epsilon scaling shows
that this equivalence preserves the original scalar action.

When `G` is affine over its base, `kernelBaseChangeLinearEquiv` is the resulting
`A`-linear equivalence between the actual Lie kernels. It is natural under
every `K`-algebra homomorphism, regarded as a `k`-algebra homomorphism on the
original group. It intertwines the actual adjoint actions at every `A`-point:
the proof uses preservation of multiplication, inversion and constant
dual-number points.

There is no field, finite-type, smoothness, reductivity, reducedness or
nontriviality hypothesis. This comparison concerns the actual scheme pullback;
it does not itself construct a tensor scalar-extension map or identify
weight-space support.
