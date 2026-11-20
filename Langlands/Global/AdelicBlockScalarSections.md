# Scalar sections for adelic block induction

Let \(P=UM\) be the actual upper block parabolic in the adelic general linear group \(G\), and let \(K\) be the standard compact subgroup. Write \(\mu:P\to M\) for the diagonal-block projection and \(\delta^{1/2}\) for the constructed positive half character. Fix a complex subspace \(W\) of scalar functions on \(M\).

`ScalarSections` consists of functions \(f:G\to\mathbb C\) invariant under \(U\) on the left whose normalized Levi slice

\[
\Phi_f(k)(m)=\delta(m)^{-1/2} f(mk)
\]

belongs to \(W\) for every \(k\in K\). The corresponding `CompactSections` are functions \(\Phi:K\to (M\to\mathbb C)\) with values in \(W\). They satisfy

\[
\Phi(pk)(m)=\delta(p)^{1/2}\,\Phi(k)(m\mu(p))
\qquad(p\in P\cap K,\ k\in K,\ m\in M).
\]

The restriction map uses the normalized slice. To prove its covariance, factor \(mp\) by the unipotent radical and the Levi. Left unipotent invariance removes the first factor. The identity \(\mu(mp)=m\mu(p)\) and multiplicativity of the half character give the covariance formula.

The published Iwasawa decomposition factors any \(g\in G\) as \(pk\). An upper triangular parabolic factor belongs to the given block parabolic. The extension evaluates \(\delta(p)^{1/2}\Phi(k)(\mu(p))\). If \(pk=q\ell\), then \(q^{-1}p\in P\cap K\) and \((q^{-1}p)k=\ell\). Compact covariance and the two multiplicative maps show that the values from the two factorizations agree. The extension is left \(U\)-invariant and its normalized Levi slices recover \(\Phi\). The two maps give `compactPictureEquiv`. Right translation by \(K\) preserves the scalar section carrier because the translated slices are slices at other compact elements.

For actual block realizations \(S_i\), `coefficientValues` is the span of the products of their vectors evaluated on the diagonal blocks of \(m\). `RealizedSections` uses this space for \(W\). Each vector is rationally invariant in its own block. Linearity extends this invariance to the span. The half character is one on rational parabolic points by the product formula, so `realizedSection_rational` gives left invariance under the rational parabolic. This applies in particular when each \(S_i\) is the operator realization of a supplied cuspidal representation.

The carrier and linear equivalence are internal algebraic constructions. Langlands (1979), proof of Proposition 2, pp. 204–205 (PDF 199–200), uses scalar functions invariant under the adelic unipotent radical and the rational parabolic, with cuspidal Levi slices. Getz and Hahn (2024), §10.1, pp. 270–271 (PDF 282–283), describe the compact model and how the inducing twist changes between the global and local conventions. The Lean carrier records coefficient membership at compact arguments. Smoothness, compact finiteness, differential equivariance and factorization into the prescribed local modules require further arguments.
