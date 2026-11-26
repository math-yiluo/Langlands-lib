# Compact conditions for the normalized adelic convolution

`NormalizedConvolutionCompactConditionsStatement` uses a closed subgroup
\(P\) of an affine group \(G\), locally of finite type over a number field, with a
supplied maximal compact \(K\) satisfying \(P(\mathbb A)K=G(\mathbb A)\).
The kernel satisfies `IsLeftFiniteTestFunction` for the archimedean
factor \(K_\infty\). It is continuous and compactly supported, its left
\(K_\infty\)-translates span a finite-dimensional space, and it is left
invariant under an open finite adelic subgroup. The normalized
convolution is right \(K_\infty\)-finite for each continuous input and
each complex parameter. A single open finite right level fixes the
output for all inputs and parameters.

`normalizedConvolutionCompactConditions` uses the fact that untwisting
the right convolution of the twisted input gives
`IsIwasawaCompact.inducedConvolution`. The untwisting multiplier is
right invariant under \(K\).

A right shift by \(k\) in the infinite compact corresponds, by
left invariance of Haar measure, to replacing the kernel
\(\phi(h)\) by \(\phi(k^{-1}h)\). Each kernel in the span of these left
translates is continuous with compact support. At each adelic point,
its product with the twisted translates of the continuous input is
integrable. Integration thus defines a linear map on the span. Left
\(K_\infty\)-finiteness makes its image finite-dimensional, and that
image contains the right compact orbit of the convolved output. The
common finite level is the intersection of the kernel's open left
level and the finite factor of \(K\).

`IsIwasawaCompact.integral_translate_left_equivariant` proves that
normalized convolution also preserves any scalar left equivariance
relation at a point of the parabolic. The two height factors contributed
by the parabolic element are inverse and cancel before integration.
This applies to the invariance and split-component equivariance
conditions of the inducing forms.

The action is the normalized form of the compact realization in Arthur,
*An introduction to the trace formula*, §7 pp. 32–34, with the
half-modulus in the inducing form as in Lapid, *On Arthur’s Asymptotic
Inner Product Formula of Truncated Eisenstein Series*, §2, p. 311.
