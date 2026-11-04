# Dimension of quotients by smooth connected kernel cores

This derived unit concerns the actual quotient constructed in
`KernelCoreQuotient`. Let `k` be an algebraically closed field in an arbitrary
universe, `G` a smooth affine group scheme over `k`, and `f : G ⟶ A` an actual
homomorphism to a separated group scheme. The core is the reduced identity
component of the full scheme kernel of `f`; the quotient and its descended
homomorphism are the existing `KernelCoreQuotient.groupScheme f` and
`KernelCoreQuotient.factor f`.

The principal result `KernelCoreQuotient.smoothOfRelativeDimension_one` says
that, if `G` is connected, `f` is nonzero, and `A` is smooth of relative
dimension one, the actual quotient is smooth of relative dimension one.
There is no characteristic restriction and no unipotence hypothesis. The
more general `exists_relativeDimension_le` requires connectedness and a
smooth target of relative dimension `n` and supplies a relative dimension
`m ≤ n` for the quotient, without requiring `f` to be nonzero.

## The actual kernel and the identity fiber

`ReducedSubgroup.isOpen_range_identityCoreι` proves that the underlying
range of the reduced identity core of an affine locally finite-type group is
open in the full group. The identity component of the reduction is open;
the reduction map identifies its underlying topology with that of the
original group, and the existing `isOpen_image_redι` transports this open
set.

The general helpers `range_zero_hom` and `hom_identityPoint` identify the
range of the zero homomorphism with the identity singleton and prove that
homomorphisms preserve the actual identity point. The helper
`isClosed_singleton_identityPoint` proves that this point is closed: the
unit section over the one-point spectrum of a field is a closed immersion,
and its range is exactly that singleton.

`range_kernelι` identifies the underlying range of the full scheme-kernel
inclusion with the inverse image of the target identity. One direction is
the kernel pullback equation. The other uses joint point surjectivity of
an actual scheme pullback. Under separatedness of the target, the kernel
inclusion is a closed embedding; `kernelHomeo` therefore gives a
homeomorphism from the full kernel to this topological identity fiber.

`quasiFiniteAt_identity_of_isOpen_kernel_identity` assumes local finite
type of an actual group homomorphism and openness of the identity singleton
in its full kernel. The homeomorphism transports that open singleton to
the topological identity fiber. Transport along the equality expressing
identity preservation matches the fiber over the image of the source
identity. Mathlib's fiber homeomorphism and its open-singleton criterion
then give quasi-finiteness at the source identity.

## Application to the quotient and its dimension

`KernelCoreQuotient.inclusion_projection` proves that the quotient
projection kills the specified core by the represented fppf kernel equality.
`kernelMap` is the actual comparison from the full original kernel to the
full kernel of the descended homomorphism. The imported `FactoredKernel`
pullback theorem makes it a base change of the smooth quotient projection,
hence smooth and an open map. The equation `identityCoreι_kernelMap` shows
that it maps the open core to the identity singleton. Consequently
`isOpen_singleton_kernel_identity` proves that the identity in the descended
full kernel is isolated. This argument does not assume either full kernel
is smooth or connected.

The quotient is already locally of finite type over the field. Cancelling
the target structure morphism from the composite proves
`locallyOfFiniteType_factor`. The general fiber criterion above now gives
`quasiFiniteAt_factor_identity`.

For connected `G`, the quotient is connected and smooth, so
`smoothConnectedRelativeDimension` supplies a constant relative dimension
`m`. Apply the existing `quasiFiniteAtStalkDimension` theorem at its closed
identity point. Identity preservation identifies the image with the closed
identity of `A`. The existing closed-point stalk dimension calculation for
smooth schemes identifies the two stalk dimensions with `m` and `n`.
Their inequality proves `exists_relativeDimension_le`.

The general helper `eq_zero_of_smoothOfRelativeDimension_zero` works over a
separably closed field. A connected separated group smooth of relative
dimension zero is etale, so its structure morphism is an isomorphism by
the existing connected-etale theorem. Cancellation against that morphism
makes its identity endomorphism the constant identity map, and every
homomorphism from it is zero. For the quotient, nonvanishing of `f`
implies nonvanishing of `factor f`, which excludes `m = 0`. If `n = 1`,
the upper bound then forces `m = 1`.

## Provenance and scope

These are internal consequences of the existing actual kernel, reduced
identity core, smooth normal quotient, kernel-comparison pullback, and
published stalk-dimension and connected-etale results. The proof route
above describes the implemented Lean arguments; no additional
classification theorem or external source assertion is used.

This unit proves the dimension of an already constructed quotient.
Affineness of that quotient, its identification with the additive group,
and a finite represented split series remain separate obligations. It
does not claim global finiteness of the descended full kernel and does
not prove the host `AlgebraicallyClosedSplitSolvableStatement`.
