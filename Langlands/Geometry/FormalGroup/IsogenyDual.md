# Integral scalar-power dual isogenies

This internal assembly proves that an actual isogeny f between
scalar-divisible formal modules admits actual integral isogeny
duals for every sufficiently large scalar-power exponent.

The universal represented point of ker f gives a common threshold
above which every scalar power kills that kernel. For such an
exponent j, the actual scalar-power endomorphism of the source
therefore factors through f. The factorization theorem descends
actual points on faithfully flat covers and reconstructs their
formal power-series homomorphism, giving an actual map g with
g composed with f equal to the source scalar endomorphism.

Affine fppf local surjectivity makes f an epimorphism of actual
formal-module maps. Cancelling f and using scalar commutation
therefore gives the other composite equation on the target.
Scalar divisibility gives fppf local lifting for g, and the finite
dual-kernel theorem constructs an actual finite projective algebra
corepresenting ker g. Thus g is itself an actual isogeny.

The threshold may depend on f, but all larger exponents are
available. The coefficient ring O, its base algebra R, their
independent universes and the finite coordinate types retain the
existing generality. This is internal infrastructure for
`LocalQuasiIsogenyInverseStatement`, with no external theorem
quotation.
