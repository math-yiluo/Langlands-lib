# Norm-one partial convolutions of positive-quotient \(L^2\) classes

Write \(A=G(\mathbb A_F)\), \(A^1=G(\mathbb A_F)^1\), and \(q\) for the
projection onto the positive rational quotient. The definition
`normOnePartialConvolution` pairs a continuous compactly supported kernel
\(\kappa\) on \(A\) with the representative of an \(L^2\) class \(v\) via
\[
  \Phi_\kappa v(y)=\int_{A^1}\kappa(n^{-1}y)\,v(q(n))\,dn.
\]
The output is defined on all of \(A\).

## The positive-coordinate kernel

Use the Haar product decomposition of \(A\) into the positive central
torus and \(A^1\). Write \(p\) for the map from the positive torus into \(A\)
and \(w=p(w_+)\,w_1\) for the decomposition of \(w\). Choose a nonnegative
continuous compactly supported function \(\beta\) of integral one for the
normalized positive Haar measure. For each positive coordinate \(c\), set
\[
  k_c(w)=\beta(w_+)\,\kappa(p(c)w_1^{-1}).
\]
Whenever \(k_c(w)\ne 0\), the argument \(z=p(c)w_1^{-1}\) lies in the
support of \(\kappa\), its positive coordinate is \(c\), and
\(w=p(w_+)z^{-1}p(z_+)\). Thus all \(k_c\) have support in a common
compact set. Their sup norms are bounded by the product of the sup norms
of \(\beta\) and \(\kappa\).

`integrable_normOnePartialConvolution` uses the ambient locally integrable
pullback of \(v\) and the compactly supported kernel obtained from
\(w\mapsto\kappa(wy)\) at \(c=1\). In product coordinates, integrating its
absolute value in the positive coordinate leaves the norm of the partial
convolution integrand. The identity `normOnePartialConvolution_eq_smoothing`
uses \(c=y_+\). The quotient map removes the positive factor in the pullback
of \(v\). Integrating \(\beta\) and substituting \(n\mapsto y_1 n\) shows
that \(\Phi_\kappa v(y)\) equals the full right convolution
`positiveQuotientLpSmoothing` by \(k_{y_+}\) at \(y\).

An integrable majorant of \(\lvert v(q(n))\rvert\) on a compact set of
norm-one points comes from a compactly supported kernel equal to one on the
inverse compact set. This majorant supplies dominated convergence for
continuity. Left invariance under \(G(F)\) follows by a change of variables
in \(A^1\). Each right invariance of \(\kappa\) passes to \(\Phi_\kappa v\).

## Growth, cuspidality, and composition

`exists_normOnePartialConvolution_growth` bounds a point evaluation of
\(\Phi_\kappa v\) by \(C_\kappa H(y)^R\lVert v\rVert_2\), with one
exponent \(R\) for all continuous compactly supported kernels. Apply the
`quotientConvolutionKernel` reproducing-kernel estimate to \(k_{y_+}\).
Its uniform support and sup norm reduce the estimate to the mass assigned
by the positive rational subgroup Haar measure to the intersection with
the conjugate by \(y\) of a fixed compact set. The polynomial mass bound
`adelicPositiveRationalConjugateGrowth_allPoints` controls the norm of the
reproducing vector, and Cauchy–Schwarz gives the estimate linear in
\(\lVert v\rVert_2\).

`normOnePartialConvolution_hasZeroProperParabolicConstantTerms` uses the
containment of each proper parabolic radical in \(A^1\). Along the radical
orbit of \(y\) the positive coordinate stays \(y_+\), so the constant term is
that of full right convolution by a single kernel \(k_{y_+}\). The integrated
right action preserves the cuspidal submodule. The continuous convolution
represents that action, so `groupSchemeFullAEL2ContinuousCuspidality` and
the comparison of normalized and representative-based constant terms give
pointwise vanishing.

For \(R(k)f(y)=\int_A k(a)f(ya)\,da\), the Fubini identity
`normOnePartialConvolution_rightConvolution` gives
\(\Phi_{R(k)\phi}v=R(k)(\Phi_\phi v)\). With \(y\) fixed, the two kernels
confine \(n\) to \(\{y\}\operatorname{tsupp}(k)\operatorname{tsupp}(\phi)^{-1}\)
where the product integrand is nonzero. The integrable majorant on this
compact set justifies the exchange of integrals. Integrability for each
kernel also gives additivity over finite sums.

The growth argument adapts Mœglin–Waldspurger, *Spectral Decomposition and
Eisenstein Series* (1995), I.2.4–5, printed pp. 25–27 (PDF pp. 8–10).
The registered source is `moeglin-waldspurger-1995-growth-and-constant-terms`,
SHA-256 `296dcb3e7170bb0c2689cf0c79136a43cd86976df2b4c51f027cf9365f7fe988`.
The positive-coordinate kernel transfers the ambient quotient-convolution
argument to integration over \(A^1\).
[Chapter I, Part 2](https://doi.org/10.1017/CBO9780511470905.004)
