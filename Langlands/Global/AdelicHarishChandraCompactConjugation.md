# Convolution equations under infinite compact conjugation

`Langlands.Global.HarishChandraCompactConjugationStatement` fixes a
connected reductive group, one parabolic, an Iwasawa compact \(K\), and
an infinite adelic point \(t\). Write \(K'=t^{-1}Kt\) and use the
corresponding height for each compact. A uniform convolution equation
for the \(K'\)-twists of \(f\) gives a uniform convolution equation for
the \(K\)-twists of \(x\mapsto f(xt)\), with the same scalar coefficients
and base parameter.

The transported kernels are \(h'_j(y)=h_j(t^{-1}yt)\). Conjugation is
a smooth change of variables on the infinite slices and is the
identity on pure finite points. It therefore preserves compact
support, smoothness and both finite level conditions. The right
compact translate span of \(h'_j\) lies in the pullback of the
corresponding translate span of \(h_j\) under the conjugate compact.
Conjugation commutes with inversion, giving the second finiteness
condition. It also leaves the finite coordinate of every point
unchanged.

The convolution formula changes variables by \(y\mapsto t^{-1}yt\),
using both left and right invariance of the connected reductive
adelic Haar measure. The published conjugation identity for Iwasawa
heights gives a factor depending on \(t\) and the parameter only.
This factor multiplies both sides of the equation and can be
cancelled since the height power is nonzero.

This is a derived transport for the uniform convolution equation
in Bernstein–Lapid, *On the meromorphic continuation of Eisenstein
series*, §8.3, Lemma 8.3, p. 223
(`bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`,
SHA-256 `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`).
