# Coefficient extension of the generic Lie algebra and the integral Lie lattice

`GenericLie.baseChange` extends a dual-number tangent point from a field to an
extension field and uses the inverse of `Lie.kernelBaseChangeLinearEquiv` to
regard it as a tangent point of the actual base-changed group. For a commuting
square of coefficient rings and fields, it is semilinear over the map of
coefficient rings.

`IntegralModel.lieMap_baseChange` identifies the generic image of an extended
integral tangent point with the extension of its original generic image. The
proof compares the two paths through the coefficient square by projecting the
specified generic-fibre comparison to the original model. Both paths apply the
same map of dual-number coefficients. `IntegralModel.baseChange_mem_lieLattice`
then follows by taking the image of the extended integral tangent point. These
constructions use the fraction fields and affine models and require no
smoothness hypothesis.

The construction supplies the Lie-lattice arrow for coefficient functoriality
in Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach*, Proposition A.5.19(3)
and Remark A.5.20, pp. 642–643 (PDF pp. 673–674).
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

The additive map `GenericLie.baseChangeMap` and its integral lattice comparison are defined in [LieLatticeCoefficientExtension](LieLatticeCoefficientExtension.md).
