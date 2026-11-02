# Affine Lie kernels and identity derivations

This module constructs a linear comparison for the actual dual-number identity
kernel. Its source conventions are Milne, *Algebraic Groups* (2017), §§10.6,
10.11 and 10.18–10.20 (printed pp.188–189,191–192; PDF204–205,207–208).
The coordinate-algebra implementation and its extension to arbitrary commutative
base rings, arbitrary commutative test algebras, and affine group schemes without
finite-type or smoothness assumptions are derived. The comparison uses only the
published actual kernel and its module operations.

`derivationLiftEquiv` expresses a derivation as the second coefficient of an
algebra homomorphism into dual numbers with fixed first coefficient. Its inverse
reads that second coefficient. The algebra map laws are exactly linearity and
the Leibniz identity; equality of both coefficients proves the inverse laws.

`coordinatePresentation` chooses a presentation of the given affine group
scheme as a relative spectrum using Mathlib's essential-image characterization.
`coordinateAlgebra` and `coordinateIso` retain this same choice.
`pointCoordinates` uses full faithfulness of relative spectrum to identify actual
affine scheme points with coordinate-algebra homomorphisms. The equivalence is
natural under every coefficient-algebra homomorphism. `coordinateOrigin` is the
coordinate map of the identity point. The test algebra carries the coordinate
algebra's action through this augmentation, as specified by
`coordinateOriginAlgebra`; `coordinateOriginScalarTower` proves its agreement
with the original base-algebra structure. `IdentityDerivation` means derivations
with this precise coefficient action.

`kernelCoordinates` restricts the point-coordinate equivalence to the actual
identity kernel: reduction is projection to the first coefficient, so its kernel
condition says exactly that this coefficient equals the augmentation followed
by the structure map. Composing with `derivationLiftEquiv` gives
`kernelDerivationEquiv`. Its value on a coordinate is the second coefficient of
the original point's algebra map.

`kernelDerivationEquiv_scale` uses naturality and the actual epsilon-scaling
map to identify scalar multiplication. For `kernelDerivationEquiv_mul`, the
proof embeds two kernel points into independent square-zero directions over
`A ⊕ A` and multiplies them there. Projection to either direction recovers the
corresponding original point; summing the directions recovers their product.
Applying coordinate naturality to these three linear maps says that the second
coefficient of the product is the sum of the original second coefficients.
Thus `kernelDerivationLinearEquiv` respects the already constructed kernel
module; no new operations are transported onto its carrier.
`kernelDerivationEquiv_naturality` states coefficientwise compatibility with
every test-algebra homomorphism.

This module proves neither a tensor-product base-change equivalence nor a
finite-dimensionality theorem or the weight decomposition. Those are subsequent
prerequisites and results.
