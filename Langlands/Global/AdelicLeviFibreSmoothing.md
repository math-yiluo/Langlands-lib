# Smoothing a family of norm-one Levi classes

Let \(P=MU\) be a standard parabolic of \(G\) over a number field \(F\), and
fix \(\beta\in C_c(G(\mathbb A),\mathbb C)\). Let \(L(g,m)\) be the integral
of \(\beta(g^{-1}u\,\iota(m))\) over \(U(\mathbb A)\) with Mathlib's Haar
measure. Use a supplied central split torus in \(M\) whose restriction on
rational characters is injective with finite-index image. Write \(p(b)\) for
the image in \(M(\mathbb A)\) of a positive point \(b\) of this torus.
The kernel `leviFibreSmoothingKernel` at
\((g,b)\) is the compactly supported function
\[
 z \longmapsto \overline{L(g,p(b)z^{-1})}.
\]
The weighted evaluation `leviFibreSmoothingIntegrand` applies norm-one
partial convolution with this kernel at a norm-one point \(x\) and multiplies
by the inverse Levi modulus at \(p(b)\). `leviFibreSmoothing` evaluates at
\(x=1\) and integrates against Haar measure on the positive subgroup, scaled
so its product with norm-one Haar corresponds to the fixed Levi Haar.
The class \(w(b)\) lies in \(L^2\) on the quotient of \(M(\mathbb A)\) by
the rational points and the image of the positive subgroup. The measure on
that quotient is transported from \(M(F)\backslash M(\mathbb A)^1\).

For \(g\) in a compact set, the radical kernels have a common compact support
in the Levi. Its image under the positive factor map contains the positive
support of the weighted evaluations. This holds for every \(x\) and every
class, since the product of two norm-one points has trivial positive factor.
For right-invariant norm-one Haar and a continuous \(L^2\)-valued family \(w\),
the weighted evaluation and smoothed function are continuous, and the
positive integral is integrable. Locally in \((g,b,x)\), the reflected
kernels translated to \(x\) have a common compact support. They are jointly
continuous in the parameters and the Levi variable. The norm-one
kernel-vector construction therefore gives a continuous family of vectors
in \(L^2\), and pairing with \(w\) gives joint continuity of the weighted
evaluation. Integrating on a fixed compact positive support near each \(g\)
gives continuity of the smoothed function.

Multiplying \(g\) on the left by \(\iota(p(a)x)\) and replacing \(b\) by \(ab\)
changes the evaluation at \(1\) to an evaluation at \(x\). Centrality of
\(p(b)\) gives the required equality of Levi arguments. The covariance
factor of the radical kernel cancels the extra modulus in the weight, because
the modulus at \(x\) is one. Left invariance of positive Haar measure gives
the corresponding identity for the smoothed function. Radical invariance of
the kernel and rational invariance of norm-one partial convolution give
left invariance under \(U(\mathbb A)M(F)\).

The radical integration and inverse-modulus weight come from
Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series*, I.1.13.
Mathlib's radical Haar is a positive multiple of the Haar measure normalized
there by giving the rational radical quotient volume one. The comparison is
given by `exists_integral_adelicRangeMap_eq_normalized`. The reflected
kernel and the positive-point integral provide an internal smoothing
construction for the norm-one Levi pairings in
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*,
§6.2, (6.8).
