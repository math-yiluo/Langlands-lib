# Local quasi-affine models from the multiplicative-type quotient statement

This is an internal conditional reduction. It takes a proof of the existing
`RelativeMultiplicativeTypeQuotientStatement` as an explicit hypothesis.
It does not supply that proof or assert the main maximal-moduli target
unconditionally.

`quasiAffineOver_of_fixedMaximalTorus` assumes a smooth affine ambient group,
a supplied universal closed fibrewise maximal relative-torus family, and
a fixed closed fibrewise maximal relative torus over the base. The torus
is of relative multiplicative type. The assumed quotient statement gives
a closed representative of its full normalizer and an actual homogeneous
quotient that is relatively quasi-affine. The previously constructed
normalizer-quotient isomorphism transports that property to the supplied
parameter scheme above every affine open of the base.

`quasiAffineLocalCoverOfQuotient` returns an actual etale cover together
with relative quasi-affineness of the parameter scheme pulled to every
cover member. The ambient group is reductive over the arbitrary original
base. Use published etale-local existence to choose a maximal torus on
each member. The supplied universal family remains closed, a relative
torus, fibrewise maximal, and universal after arbitrary base change.
Apply the fixed-torus result on each member. The cover may be infinite.

`maximalTorusModuliQuasiAffine_of_quotient` applies the generic
`QuasiAffineEtaleDescent.quasiAffineOver_of_etaleCover` theorem to this
cover. Its conclusion is exactly the unchanged
`MaximalTorusModuliQuasiAffineStatement`, still conditional on the
explicit general quotient theorem hypothesis. No proof of
`MaximalTorusSchemeStatement` is used. The descent proof is the separate
construction in `Langlands.AlgebraicGeometry.QuasiAffineEtaleDescent`.
