# Harris representatives with the ordinary polarization

On a connected admissible base fix a geometric point and an original
Harris level inside the integral adelic stabilizer. An original
`TateNormalizedCMRepresentative` has a primitive homomorphism `μ` with
original polarization `k • μ` for some positive integer `k`.
`tateNormalizedCMQuadrupledRepresentative` keeps the same abelian
scheme, dual, original action, and integral restriction. It uses
`primitivePolarization_four_isPolarization` and
`harrisRescalePolarization` to replace the polarization by `4 • μ`
with the original positive auxiliary involution. The ratio `4/k`
provides the rational multiple equation for the identity isogeny.
The original Weil-level transport along that isogeny gives the new
invariant orbit. The source lattice criterion shows that it is
normalized, since the identity on the full rational Tate module
retains the full integral Tate image.

The uniform degree index for the quadrupled primitive homomorphism
therefore measures the literal polarization of the new representative.
This is `tateNormalizedCMQuadrupledRepresentative_degree`.

`tateNormalizedCMQuadrupledRepresentative_ordinaryRelated` gives the
original ordinary relation between these two representatives. The
identity of the abelian scheme gives exact order equivariance and
induces the rational identity. Its multiple and level equations are
those used in the construction.
