# From ambient Siegel decay to the norm-one Levi integral

`AdelicLeviSiegelDecayStatement` fixes an algebraic Siegel setup and a closed
matrix embedding of positive dimension. It takes an ordinary split-component
eigenvector with unitary normalized parameter, continuity, parabolic left
invariance and the bound in `HasSiegelLogDecayAlongLevi`. That bound requires
every inverse power of the torus logarithmic height, relative to the square
root of the ambient Siegel modulus. It holds on weak chambers of the positive
derived split torus where the simple-root logarithms outside the Levi index
are bounded above, uniformly over compact sets of right factors. The
conclusion is integrability of the absolute square on the given compact
subgroup times the norm-one Levi quotient, with probability Haar measure
on the compact and quotient Haar measure on the Levi.

For the Levi chamber estimate, lift the positive Levi coordinate through
the common maximal split torus into the ambient positive Siegel torus.
The Levi coordinate has norm one, so its ambient image does also. The
positive split-component correction bounds the omitted logarithms and
preserves the selected logarithms. Bounds for rational character norms and
their inverses in a closed embedding bound the absolute selected logarithms
by the corrected ambient logarithmic height. The norm of the eigencharacter
is the square root of the modulus of the correction. The ambient modulus is
a product of powers of root norms, so it factors across the correction and
the original torus point. The eigencharacter cancels the correction factor.
The original ambient modulus equals the Levi modulus at the common norm-one
point.

The Levi compact prefix can be placed after its positive coordinate. The
unipotent conjugates are in one compact set, and the minimal Levi commutes with
the torus. The image of the resulting compact family times the pairing compact
serves as the family of right factors in the chamber estimate. Squaring
supplies the majorant of `exists_normOneSiegelIntegralBound` on the fixed
Levi chart. The constant is uniform over the pairing compact, and continuity
on the quotient and Tonelli's theorem give integrability on the product.

Delorme's Lemma 3.10(i) reduces the square-integrability claim to the
corresponding claim on the Levi using Lemma 3.8(iv). The estimate here
implements the Levi transfer and integral comparison for an eigenvector
with a supplied ambient decay bound.

Delorme, *On the spectral theorem of Langlands*, Advances in Mathematics 426 (2023),
109107, published PDF pp. 7–8 and 14–16, (2.4)–(2.5) and Lemmas 3.8 and 3.10.
