# Convolution factors of an adelic smoothing weight

Let \(G\) be an affine group scheme locally of finite type over a number field \(F\).
Use `AdelicGroupPoints.split` to write an adelic point as \((x_\infty,x_f)\).
Let \(m_\infty\) and \(m_f\) be Haar measures on the two factors. The measure \(m\)
on the adelic group is the image of their product under the inverse splitting.

For a continuous compactly supported function \(f\) on the infinite group and a
finite Hecke test \(g\), put
\[
  W(g,k)(x)= f^{*(k+1)}(x_\infty)\,g(x_f).
\]
This is `adelicSmoothingWeight`. The definition `adelicSmoothingCompactTest`
packages the weight as a compactly supported continuous function. The support
of the product function lies in the product of the two topological supports.
The homeomorphism then gives compact support on the adelic group.

Let \(K\) be a compact open subgroup of the finite group and \(e_K\) its
indicator normalized by \(m_f(K)^{-1}\). For a test \(g\) invariant under
left multiplication by \(K\), `AdelicSmoothingConvolutionStatement` gives
\[
  W(e_K,0)*_m W(g,k) = W(g,k+1) \qquad (k\ge 0).
\]

`adelicSmoothingConvolution` transports the convolution to the product
using `convolutionIntegral_comp_continuousMulEquiv`. There
`convolutionIntegral_prod_tensor` reduces it to two convolutions. The infinite
convolution is the next power by `convolutionIntegral_positiveConvolutionPower`.
The finite convolution equals \(g\) by
`HeckeAlgebra.normalizedIndicator_mul_of_leftInvariant`.

The factorization expresses the smoothing weights as convolution tests for
the comparison motivated by Arthur–Clozel, *Simple Algebras, Base Change, and
the Advanced Theory of the Trace Formula* (1989), Ch. 1, §4, formulas
(4.4)–(4.7), printed pp. 43–44 (PDF pp. 57–58). The formula above follows from
the product Haar measure and the Library's convolution identities.

Source ID `arthur-clozel-1989-base-change`,
SHA-256 `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
