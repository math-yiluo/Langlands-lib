# Products of smooth adelic test kernels

`Langlands.Global.AdelicGroupPoints.positiveConvolutionPower h j` is the
\((j+1)\)-st left-Haar convolution power of a function \(h\) on the actual
adelic group. For functions \(h,k\), the product uses
\[
 (h*k)(x)=\int h(y)\,k(y^{-1}x)\,dy.
\]
The action is `rightConvolution`, with
\(\delta(h)f(x)=\int h(y)f(xy)\,dy\).

The proof writes \(h*k=\delta(\check k)h\) and
\(\widecheck{h*k}=\delta(h)\check k\), where \(\check k(x)=k(x^{-1})\).
The first identity follows by a left Haar substitution. Inversion is smooth
on the archimedean group and exchanges the two finite-adelic invariances of
a test function. The published right-convolution smoothing theorem therefore
gives smoothness of the product and its right finite-level invariance.
Left invariance comes from \(h\). The support lies in the product of the
two compact supports. The two identities also apply the published
compact-finiteness lemma to the product and to its inversion, with right
compact finiteness contributed by \(k\) and left compact finiteness by \(h\).

`rightConvolution_convolutionIntegral` proves
\(\delta(h*k)f=\delta(h)\delta(k)f\) for continuous compactly supported
kernels and continuous \(f\). The proof exchanges the integrals on a compact
support in the product and substitutes \(z=yt\) in the inner integral.
`rightConvolutionEnd` packages convolution by a test kernel as a
complex-linear endomorphism of the continuous functions. Induction gives
the support, smoothness, compact-finiteness and operator-power properties
for every positive power.

The construction implements the test kernels underlying the powers of
\(\delta(h)\) in Bernstein–Lapid, *On the meromorphic continuation of Eisenstein
series*, §8.3, Lemma 8.3, journal p. 223
(`bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`,
SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`).
