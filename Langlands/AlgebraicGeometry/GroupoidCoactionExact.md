# Kernel coactions and transport

Author: Worker 101.

This is an internal algebraic construction derived from the published
coaction formulas and the universal-point constructor in
`GroupoidCoactionUniversal`. The published definitions remain unchanged.
Rings lie in arbitrary universe `u`; both modules lie in independent
universe `v`. No Noetherian or affine-descent theorem is assumed.

Tensor maps commute with maps of the module factor, and tensoring a linear
map respects the left algebra's scalar action. Both facts follow by tensor
induction or by the algebra-linear tensor map. The same naturality holds
for `coactionCompose`: equivariance lets the module map pass through the
two successive coactions. The proof reduces this equality to pure tensors.

`semilinearMap` expresses the published additive coaction as a map
semilinear for the target ring homomorphism. `ofInjective` constructs a
coaction on a module with a supplied semilinear map and an injective linear
map intertwining it with an existing coaction. Its unit and cocycle laws
are checked only at the universal diagonal and composable points, where
tensoring the injection remains injective. Their source algebras are flat,
as proved by the universal-point helper. Its `ofUniversal` constructor then
supplies the identities at every test ring. In particular this argument
never requires an arbitrary test ring to be flat.

`ofSurjective` transports a coaction through a surjective linear map when
a compatible semilinear map on the target is supplied. Choosing a preimage
and applying tensor naturality proves its pointwise unit and cocycle laws
directly. This construction does not yet construct a cokernel's underlying
semilinear map.

For an equivariant map `f`, flatness of the source algebra identifies the
tensor of `ker f` with the kernel of the tensored map, using Mathlib's
`LinearMap.tensorKerEquiv`. Restricting the source coaction to this tensor
kernel and applying the inverse equivalence gives `kernelSemilinearMap`.
Its tensor inclusion is the original coaction. Finally `kernel` applies
`ofInjective` to the kernel inclusion; source flatness follows from the
relation's source étaleness. `kernel_subtype_isHom` verifies that this
inclusion is equivariant.

This file constructs kernel coactions and injective/surjective transport.
It does not construct cokernel coactions, prove exactness of invariants for
arbitrary surjections, or prove the Serre criterion.
