# Polynomial growth of continuous adelic convolution representatives

`Langlands.Automorphic.GroupSchemeFunctions.groupSchemeQuotientL2ConvolutionPolynomialBound`
proves `GroupSchemeQuotientL2ConvolutionPolynomialBoundStatement` for the
original positive rational quotient, its Haar measure and the integrated
right action. The bound holds at every adelic representative for every
input in the quotient \(L^2\).

Fix the matrix embedding \(\rho\) and write \(H_\rho\) for its adelic
height. `adelicRationalConjugateCountingAllPoints` gives a natural exponent
\(d\) that works for every compact set in the ambient adelic group. For a
weight \(f\), put \(S=\operatorname{supp}(f)\operatorname{supp}(f)^{-1}\),
using topological support, and let \(C_0\) and \(C_1\) be its compact
images under the positive and norm-one projections, respectively. We view
\(C_1\) in the ambient adelic group. The positive projection takes the same
value on \(s\) and \(xsx^{-1}\). Centrality of the positive factor makes the
norm-one projection commute with conjugation by \(x\).

By `measurePreserving_positiveRationalDecomposition`, the positive rational
subgroup has the product of normalized positive Haar measure \(\nu\) and
counting measure on the norm-one rational subgroup. The preimage of the
subgroup's intersection with \(xSx^{-1}\) lies in the product of \(C_0\)
with a finite set of norm-one rational points that injects into
\(G(F)\cap x C_1 x^{-1}\). The counting bound \(K H_\rho(x)^d\) for that
intersection gives the subgroup mass bound \(\nu(C_0) K H_\rho(x)^d\).

`groupSchemeQuotientL2ContinuousRepresentative` gives a continuous \(\psi\)
equal almost everywhere to the integrated output. With \(M\) a nonnegative
uniform bound for \(|f|\) from compact support, the squared pointwise
estimate is
\[
|\psi([x])|^2 \le M\,\|f\|_{L^1(\mu_G)}\,\nu(C_0) K\, H_\rho(x)^d\,\|\phi\|_2^2.
\]
Since \(H_\rho(x)^d\ge 1\), it is bounded by its square. Taking the square
root of the resulting bound gives \(B_f H_\rho(x)^d\|\phi\|_2\), where
\(B_f=\sqrt{M\,\|f\|_{L^1(\mu_G)}\,\nu(C_0)K}\) and \(d\) is independent
of both \(f\) and \(\phi\).

The conjugate count is the case \(y=x\) of Mœglin–Waldspurger,
*Spectral Decomposition and Eisenstein Series* (1995), I.2.4 Lemma (a)(i).
The resulting estimate corresponds to the function-value part of I.2.5
Lemma (b), which applies to smooth weights and square-integrable functions
modulo the centre with a unitary central character. The Lean estimate uses
continuous weights on the positive rational quotient. The passages are on
printed pp. 25–27 (PDF pp. 8–10 of
`05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`, registered as
`moeglin-waldspurger-1995-growth-and-constant-terms`, SHA-256
`296dcb3e7170bb0c2689cf0c79136a43cd86976df2b4c51f027cf9365f7fe988`).
For a connected reductive group with its split component, the quotient and its
measure use the convention of Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), (2.19)–(2.22), printed pp. 68–69 (PDF pp. 85–86,
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`).
