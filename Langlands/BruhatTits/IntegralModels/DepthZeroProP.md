# Discrete parahoric reduction and pro-p inverse images

This internal adapter uses supplied relative-component model data `D`
over the valuation ring of a nonarchimedean local field `F` and supplied
special-fibre quotient data `Q`. The generic group scheme is affine and
locally of finite type. Its actual rational points carry the canonical
point topology. The rational points of `Q.quotient` carry the discrete
topology throughout this module.

`localFieldReductionContinuousHom` bundles the actual
`Q.parahoricReduction` on `D.neutral.integralPoints` as a continuous
homomorphism. Its continuity does not require the radical or fppf-quotient
hypotheses: the kernel contains the level-one congruence subgroup viewed
inside the integral-point image. The published local-field congruence
neighborhood theorem makes that subgroup open. The reduction kernel is
therefore open. A homomorphism to a discrete group with open kernel is
continuous at the identity, hence everywhere.

For any subgroup `P` of the quotient point group,
`localFieldReductionPreimage P` is the open subgroup of the original
generic rational-point group whose underlying subgroup is

`(P.comap Q.parahoricReduction).map D.neutral.integralPoints.subtype`.

Its relative inverse image is open by continuity into the discrete
target. The neutral integral-point image is open in the ambient group,
so its subtype inclusion maps this open subgroup to an ambient open
subgroup. The lift lies inside the actual integral-point image, and its
`subgroupOf` there equals `P.comap Q.parahoricReduction`.

Under the represented fppf-quotient hypothesis,
`localField_isProP_ker_parahoricReduction` transports a supplied pro-p
property of `Q.positivePoints` to the actual reduction kernel using
`ker_parahoricReduction`. That equality identifies the kernel with
`Q.positivePoints.subgroupOf D.neutral.integralPoints`; the pro-p
transport theorem preserves the twice-induced topology.

`localField_isProP_reductionPreimage` then proves that the ambient lift
of any abstract p-subgroup `P` is pro-p. The neutral integral-point image
is compact by the published integral-point compactness theorem and is
totally disconnected by the canonical affine point topology. The pro-p
inverse-image theorem applies inside that compact group. The subgroup
transport theorem returns the result to the ambient rational points.
No surjectivity, finiteness or reductivity of the quotient is used in
this lifting argument.

Conversely, `localField_isPGroup_reductionImage` proves that every pro-p
subgroup contained in the integral-point image has p-group image under
the actual reduction. It views the subgroup inside the integral points
with the same topology and applies the discrete-image theorem.

The provenance consists of the published reduction-kernel computation,
integral-point topology and congruence neighborhood results, together
with the elementary pro-p transport, inverse-image and discrete-image
lemmas. This module assumes the pro-p property of the radical preimage
explicitly in the two lifting results; it does not prove that separate
local-model theorem. It constructs no models or quotients and proves no
finite-field Sylow classification or maximal pro-p conclusion.
