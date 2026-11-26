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

`normalizedConvolutionCompactRestriction` gives one finite-dimensional
space of functions on \(K_\infty\) for a fixed left-finite kernel.
It contains the compact restrictions
\(k \mapsto (\phi *_\lambda v)(gk)\) of the normalized convolutions for
every continuous input \(v\), complex parameter \(\lambda\), and adelic
point \(g\). Here \(\phi *_\lambda v\) denotes `inducedConvolution`
with kernel \(\phi\). The result uses the supplied compact Iwasawa
factorization.

Let \(W\) be the span of the kernels \(h \mapsto \phi(kh)\) for
\(k \in K_\infty\). Evaluation at \(g\) after convolution with \(v\)
at \(\lambda\) is a linear functional on \(W\). Evaluating the
functional at \(h \mapsto \phi(k^{-1}h)\) gives the value of the
original convolution at \(gk\) by the Haar substitution and the
invariance of the untwisting multiplier. The linear map from \(W^*\)
that performs these evaluations depends only on the kernel and
\(K_\infty\). Its image is the required space. This gives the compact
restriction condition in `ParabolicHarishChandraFinitenessStatement`,
which formulates the fixed compact types used in Mœglin and Waldspurger,
*Spectral Decomposition and Eisenstein Series*, I.2.17, pp. 37–38.

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
