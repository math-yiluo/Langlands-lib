# Quasi-affineness of supplied universal maximal-torus moduli

`Langlands.GroupScheme.maximalTorusModuliQuasiAffine` proves exactly the
published `MaximalTorusModuliQuasiAffineStatement.{u}` for every universe
`u`. The base scheme is arbitrary. For every reductive group scheme and
every supplied universal closed fibrewise maximal relative-torus family,
the inverse image of each affine base open in the parameter scheme is
quasi-affine.

The Lean proof applies the published conditional reduction
`maximalTorusModuliQuasiAffine_of_quotient` to the published unconditional
theorem `relativeMultiplicativeTypeQuotient`. This discharges the reduction's
only premise.

The reduction chooses an etale cover on which the reductive group admits a
maximal torus. Relative tori are of multiplicative type, so the quotient
theorem supplies a relatively quasi-affine homogeneous quotient by that
torus's full normalizer on each cover member. The normalizer-quotient
comparison identifies this quotient with the pulled supplied parameter
scheme, using its universal property for actual subgroup functors.
Arbitrary-etale-cover descent then gives the required quasi-affineness
above every affine open of the original base. These steps are implemented
in the imported `MaximalModuliLocalQuasiAffine` development, including
arbitrary base change of the supplied family.

This is a derived assembly of Library results. It uses no proof of
`MaximalTorusSchemeStatement`. No additional existence, smoothness or
surjectivity hypothesis on the supplied parameter scheme is imposed.
