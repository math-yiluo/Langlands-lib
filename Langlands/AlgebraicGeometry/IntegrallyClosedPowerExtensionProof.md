# Extending sections whose power extends

`Langlands.AlgebraicGeometry.integrallyClosedPowerExtension.{u}` proves
[`IntegrallyClosedPowerExtensionStatement.{u}`](IntegrallyClosedPowerExtensionStatement.md)
in an arbitrary universe. If a positive power of a section on a nonempty
open of an integral affine scheme with integrally closed global sections
extends to the whole scheme, the section itself extends.

The proof sends the section to its germ at the generic point.
`functionField_isFractionRing_of_isAffineOpen`, applied to the top open,
identifies the function field as a fraction field of the ring of global
sections. The germ of a restricted global section equals its image under
the algebra map into that fraction field by compatibility of germs with
restriction. Since the germ map preserves powers, the \(d\)-th power of the
germ is the image of the given global section and is therefore integral.

`IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow` applies integral
closedness to this positive power and gives a global section whose germ is
the germ of the original section. Injectivity of `Scheme.germToFunctionField`
on the nonempty open shows that the new global section restricts to the
original section.

This is the fraction-field argument of Lemma 22.23, printed p. 469,
in J. S. Milne, *Algebraic Groups* (2017), with the normality convention
in A.78, printed p. 584. The registered source is
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
