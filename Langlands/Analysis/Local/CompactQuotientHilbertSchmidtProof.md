# Hilbert–Schmidt convolution on a compact left coset space

`Langlands.QuotientIntegration.compactQuotientIntegratedHilbertSchmidt`
proves `CompactQuotientIntegratedHilbertSchmidtStatement`. It uses the given
compatible measure \(\nu\) on \(H\backslash G\), the given left invariant
measure \(\mu_G\) on \(G\), and the integrated right translation action
\(R(f)\) of a compactly supported continuous weight \(f\).

`quotientConvolutionKernel` gives a continuous family \(v(x)\) in
\(L^2(\nu)\) with the pairing formula

\[
\langle v(x),\phi\rangle = \int_G f(a)\phi(Hxa)\,d\mu_G(a),
\]

where the inner product is linear in \(\phi\). Since \(Hhxa=Hxa\) for
\(h\in H\), these pairings agree for \(v(hx)\) and \(v(x)\) against every
\(\phi\). Injectivity of `innerSL` gives equality of the vectors. The
family descends to a continuous map \(v_Q\) on the quotient. Compactness
bounds \(\|v_Q(q)\|\) by a nonnegative constant \(C\) and makes \(\nu\)
finite because \(\nu\) is finite on compact sets.

The joint right action \((q,a)\mapsto qa\) is continuous because its
composite with the open quotient map \((x,a)\mapsto(Hx,a)\) is
\((x,a)\mapsto Hxa\). Compatibility of \(\nu\) gives measure preservation
for each right translation. `integratedTranslationPointwise` identifies
\(R(f)\phi\) almost everywhere with \(q\mapsto\int_G f(a)\phi(qa)\,d\mu_G(a)\).
By the pairing formula this integral is \(k(q)(\phi)\) for
\(k(q)=\langle v_Q(q),-\rangle\). Each \(k(q)\) has norm \(\|v_Q(q)\|\).
`hilbertSchmidtUniformEvaluation` gives square summability of the images
of a Hilbert basis from the bound \(\|k(q)\|\le C\) and finite quotient
volume.

Getz and Hahn derive the Hilbert–Schmidt property in the proof of
Lemma 9.3.3 on printed pp. 247–248 (PDF pp. 259–260). Their estimate
(9.13) bounds the point evaluations of convolution uniformly, and they
use those evaluations to obtain a square-integrable kernel. The compact
coset space supplies the uniform bound here through \(v_Q\), and the
finite-measure evaluation criterion passes directly to the Hilbert basis
sums. [J. R. Getz and H. Hahn, *An Introduction to Automorphic
Representations* (2024)](https://doi.org/10.1007/978-3-031-41153-3).

The registered source is `getz-hahn-2024-automorphic-representations`,
SHA-256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
