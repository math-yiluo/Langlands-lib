# Parabolic fibres of transported convolution

Write \(w_\lambda(g)=\exp\langle\lambda,H_P(g)\rangle\) for the Iwasawa height power of an adelic parabolic. The operator transported to the untwisted function space takes \(f\) to \(w_\lambda^{-1}\delta(h)(w_\lambda f)\), where \(\delta(h)\) is right convolution. On the left parabolic fibre through \(x\), the modified kernel `IsIwasawaCompact.parabolicFibreKernel` is

\[
 t\longmapsto h(t)\frac{w_\lambda(xt)}{w_\lambda(x)}.
\]

It is continuous and compactly supported when \(h\) is. Left multiplication by \(q\in P(\mathbb A)\) adds the same character logarithm to \(H_P(xt)\) and to \(H_P(x)\). Consequently the ratio of the two height powers is independent of \(q\). The fibre formula `twistedConvolutionEnd_map_mul` integrates \(f(qxt)\) against this single modified kernel for every \(q\). In particular it applies to every point of a Levi fibre.

Let \(L\) be a subgroup of the finite adelic points whose image under the finite inclusion lies in the Iwasawa compact. If the finite projection of every point with \(h(t)\ne 0\) lies in \(L\), `twistedConvolutionEnd_rightInvariant` proves that transported convolution preserves right \(L\)-invariance. For \(l\in L\), commuting \((1,l)\) past \(t=(t_\infty,t_f)\) replaces \(l\) by \(t_f^{-1}lt_f\in L\). The input and the height power are invariant under the resulting right translations, and the inverse height power at the output is invariant under \(l\). When the height pairings are smooth on infinite slices, `twistedConvolutionEnd_smoothSlice` obtains plot-smooth output slices from smooth right convolution and multiplication by the height power at \(-\lambda\).

`twistedConvolutionEnd_eq_of_finite_support` compares two maximal Iwasawa compacts with the same infinite projection. For kernels supported over the intersection of their finite projections, the convolution of the two twisted inputs differs by the pointwise ratio of the two height powers. The same ratio cancels when the outputs are untwisted, so the transported operators agree.

The fibre formula and the finite-level arguments are derived from the Iwasawa height transformation (Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, JAMS 37 (2024), §6.2, pp. 201–202) and the transported convolution on a fixed space of inducing functions (Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series* (1995), I.4.5, printed pp. 60–62). These identities concern the operator on the function space and apply before constructing the finite-dimensional space for the Harish-Chandra equations.
