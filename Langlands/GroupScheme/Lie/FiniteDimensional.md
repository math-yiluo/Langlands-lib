# Finite dimension of the actual Lie kernel

This internal auxiliary module proves finite dimension of the published
dual-number identity kernel for an affine group scheme locally of finite type
over an arbitrary field. It uses the existing module structure on
`Additive (lieKernel G k)` and adds no smoothness, connectedness or reductivity
premise.

`finiteDimensional_identityDerivation` uses the published finite-type instance
for `Lie.coordinateAlgebra G`. Choose a finite set of algebra generators.
Evaluation on that finite set is a linear map from the derivations at the
augmentation to a finite product of copies of the base field. Mathlib's
`Derivation.ext_of_adjoin_eq_top` proves this map injective: agreement on the
generators implies agreement on the entire coordinate algebra. Its domain is
therefore finite-dimensional.

The instance `finiteDimensional_lieKernel` transports this result through the
published `kernelDerivationLinearEquiv`. In particular, the statement concerns
the original Lie kernel, with its published scalar and additive operations,
and does not replace it by an abstract finite-dimensional vector space.

The result is an internal consequence of the coordinate and derivation APIs
in `Lie.AffineCoordinates` and `Lie.GroupAlgebraCoordinates`, together with the
elementary finite-generation argument above. It is a finiteness prerequisite
for relative-root support arguments; it does not prove any root-system or
standard-parabolic structural statement.
