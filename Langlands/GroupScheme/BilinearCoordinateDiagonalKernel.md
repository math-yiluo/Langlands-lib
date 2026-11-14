# Actual diagonal kernels of bilinear coordinate groups

This derived construction works over any field `k` in arbitrary universe `u`,
with a finite index type `I`, bilinear coefficient matrices `c` and `d`, vector
coefficients `a : I → k`, and a scalar coefficient `t : k`. It assumes precisely
`IsCompatible c d (diagonalMatrix a) t`, the condition that the coordinate map
`(x, z) ↦ ((aᵢxᵢ)ᵢ, tz)` preserves the bilinear group law. No characteristic
restriction or nonvanishing condition on the individual coefficients is imposed.

`diagonalHom` is this actual group-scheme homomorphism. On every test scheme,
`diagonalHom_eq_one_iff` proves that its kernel consists of coordinates with
`xᵢ = 0` whenever `aᵢ ≠ 0`, and `z = 0` whenever `t ≠ 0`. The test scheme need
not be affine or reduced. Every nonzero field coefficient maps to a unit in
its global-section ring, which justifies cancellation even on nonreduced tests.

Write `K = {i : I // a i = 0}`. For `t = 0`,
`diagonalZeroKernelPointEquiv` restricts a pointwise kernel element to its
`K`-indexed vector coordinates and its scalar coordinate. Its inverse extends
the vector coordinates by zero. `form_restrict` identifies the full bilinear
sum with the restricted sum because both inputs vanish off `K`. This verifies
multiplicativity of the equivalence. Composing with `kernelPointsEquiv` gives
`diagonalZeroKernelCoordinates` on the actual pullback kernel. Its naturality
in all test schemes produces `diagonalZeroKernelIso`, an isomorphism to the
bilinear group with restricted source coefficients `kernelCoefficients a`.
The theorem `pointsEquiv_diagonalZeroKernelIso_hom` records its coordinate map.

For `t ≠ 0`, the scalar coordinate of every kernel point is zero.
`diagonalNonzeroKernelPointEquiv` restricts the vector coordinates, using any
finite numbering of `K`; its inverse extends them by zero and sets the scalar
to zero. Restriction preserves multiplication because the vector part of the
bilinear group law is addition. These multiplicative equivalences are natural
on every test. `diagonalNonzeroKernel_isVectorGroup` and
`diagonalNonzeroKernelIso` identify the actual kernel with the polynomial
vector group of dimension `Fintype.card K`; the latter isomorphism has the
coordinate formula `coordinates_diagonalNonzeroKernelIso_hom`.

`diagonal_kernel_properties` proves smoothness, connectedness and unipotence
of the actual kernel. In the zero-scalar case it transports these properties
from the restricted bilinear group: its underlying scheme is affine space,
and its unipotence is supplied by `BilinearCoordinateUnipotent`. In the
nonzero-scalar case it uses the corresponding vector-group properties.
This includes empty coordinate blocks and maps with all coefficients units.

Finally, `diagonal_baseChange_kernel_properties` treats any commutative ring
`R`, map `R → k`, and compatible diagonal homomorphism over `R`. The actual
base-change isomorphisms from `BilinearCoordinateBaseChange` intertwine the
specialized map with the diagonal map whose coefficients are their images
in `k`. `kernelSquareIso` identifies their actual kernels, and transports the
three properties from the field calculation. Coefficients may vanish
independently under specialization.

The provenance is the bilinear law (C.4.2) and depth-transition kernel
calculations in Kaletha–Prasad (2023), Appendix C.4, proof of Lemma C.4.4,
printed pp.700–702 / PDF pp.731–733. Source registration:
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The general diagonal-kernel construction above is derived supporting algebra.
It does not identify the actual unitary integral models, show that a root-depth
transition is diagonal in chosen coordinates, or prove the complete C.5.3 target.
