# Compactness by approximation of continuous cuspidal convolutions

`groupSchemeFullAEL2CuspidalCompactness` proves
`GroupSchemeFullAEL2CuspidalCompactnessStatement`. Write \(R\) for the
original integrated right action `fullAEL2CuspidalIntegratedAction` on
`fullAEL2CuspidalSubmodule` and \(\mu\) for Haar measure on the full
adelic group \(A=G(\mathbb A_F)\). The affine linear embedding theorem
provides a closed matrix embedding of \(G\). The positive matrix
embedding lemma handles the size-zero case and supplies the positive-size
embedding required by `groupSchemeCuspidalConvolutionCompact`. This
theorem makes \(R(h)\) compact for every smooth adelic test weight \(h\).

Let \(f\) be a continuous compactly supported weight. Choose a compact
identity neighborhood \(V\) in \(A\) and set
\(D=V\,\operatorname{tsupp}(f)\cup\operatorname{tsupp}(f)\).
Given \(\varepsilon>0\), use
`exists_rightConvolution_approximation_in_nhds` on
\(x\mapsto f(x^{-1})\) and the compact set \(D^{-1}\), with tolerance
\(\delta=\varepsilon/(\mu(D)+1)\). It supplies a smooth test weight
\(h\) supported in \(V\). Evaluating the right convolution at \(x^{-1}\)
gives the left convolution
\[
  c(x)=(h*f)(x)=\int_A h(a) f(a^{-1}x)\,d\mu(a).
\]
The approximation bounds \(\lvert c(x)-f(x)\rvert\) by \(\delta\)
on \(D\). Outside \(D\), \(f\) vanishes and the integrand for \(c\)
vanishes, since a nonzero value would require \(a\in V\) and
\(a^{-1}x\in\operatorname{tsupp}(f)\). Compactness of \(D\) gives
finite Haar measure, so \(\|c-f\|_1\le\mu(D)\delta<\varepsilon\).

`integratedActionConvolution` gives integrability of \(c\) and the identity
\(R(c)=R(h)\circ R(f)\). This composition is compact. Linearity in the
integrated weight and `norm_fullAEL2CuspidalIntegratedAction_le` bound
\(\|R(c)-R(f)\|\) by \(\|c-f\|_1\). The set of compact operators is
closed in the operator norm, so \(R(f)\) is compact.

Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
Theorem 9.1.2, printed p. 241 (PDF p. 253), establishes trace class for
smooth weights on \(A_G\backslash G(\mathbb A_F)\). Corollary 9.3.2,
printed p. 247 (PDF p. 259), applies compactness of those operators in
Lemma 9.3.1 to obtain cuspidal discreteness. The Lean proof uses the
Library's smooth compactness theorem for weights on the full adelic
group and extends it to continuous compactly supported weights by the
operator-norm estimate above. The retained source is
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
