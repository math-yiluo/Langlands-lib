# Naturality of the actual imaginary quadratic eigensheaf splitting

This internal extension of `ImaginaryQuadraticEigensheaf` works over the same
arbitrary scheme, with the same compatible global scalar structures and
imaginary quadratic field. Its additional input is an actual morphism of
module sheaves intertwining two actual unital field actions. There is no
finiteness, reducedness, flatness or nonemptiness assumption.

`sheafTensorAction_naturality` proves that this morphism intertwines the
constructed actions of every element of the global-function tensor algebra.
Tensor induction reduces this to the given field intertwining equation and
bilinearity of composition over global regular functions.
`sheafProjector_naturality` evaluates this result at the actual coordinate
idempotent.

`sheafEigenProjection_naturality` compares the actual eigenprojection after
the given morphism with the eigenprojection followed by the already
constructed restriction of that morphism to the full eigensubsheaf.
The equality is proved after the actual eigensheaf inclusion, using projector
naturality and the inclusion comparison for the restricted map. Cancelling
that monomorphism gives the stated comparison. `sheafEigenProductMap`
constructs the actual product of the two restricted maps.
`sheafEigenIso_naturality` proves naturality of the specific product splitting
with respect to this product map: its two components are the two
eigenprojection comparisons. The product is
ordered natural first and conjugate second.

All tensor actions, projectors, eigensubsheaves and decomposition maps in
these comparisons are constructed by the imported modules. Only the
original field-action intertwining equation is assumed. These are derived
results about morphisms over one fixed scheme; they do not yet compare
pullback to another scheme or construct sheaf tensor factors.
