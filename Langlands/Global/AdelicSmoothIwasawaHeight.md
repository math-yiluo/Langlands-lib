# Smooth adelic Iwasawa height pairings by convolution

`AdelicSmoothIwasawaHeightStatement` asserts that the scalar pairings of the actual logarithmic height with complex parameters are smooth on every infinite slice. It assumes an Iwasawa decomposition and a maximal compact. The height is the one obtained from the logarithmic character map and the Iwasawa decomposition in Bernstein–Lapid §2.1.

The proof constructs a nonnegative test kernel by taking a smooth infinite bump and a compact open finite level. It uses this kernel to smooth the indicator of the compact set obtained by multiplying its support on the left by the maximal compact. The resulting test kernel is left invariant under the maximal compact. Its real part is nonnegative, and its value at the identity has positive real part, so the integral of the kernel is nonzero. Openness of the finite factor supplies a left finite level for this kernel.

Convolution with the compact-invariant kernel smooths each scalar height pairing. The convolved function has the same right compact invariance and satisfies the additive parabolic covariance with the scalar term multiplied by the kernel mass. By the Iwasawa decomposition it equals the original pairing times that mass plus the convolved value at the identity. This proves the claimed smoothness using the adelic Haar measure and the actual archimedean manifold. The convolution argument is a deduction from the defining height identities and `adelicRightConvolutionDifferentiation`.

Source. Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, §2.1, p. 190, registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`, journal PDF SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`.
