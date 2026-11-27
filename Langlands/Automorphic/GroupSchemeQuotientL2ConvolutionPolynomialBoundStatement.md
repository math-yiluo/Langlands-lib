# Polynomial growth of convolution representatives on the positive rational quotient

`Langlands.Automorphic.GroupSchemeFunctions.GroupSchemeQuotientL2ConvolutionPolynomialBoundStatement`
is stated for an affine, locally finite type group scheme \(G\) over a
number field \(F\). It takes a central morphism \(i:T\to G\) from a torus
with a supplied splitting \(T\simeq\mathbb G_m^I\) for a finite set \(I\).
The pullback \(i^*:X_F^*(G)\to X_F^*(T)\) on rational characters is
injective with finite-index image. The Haar measure on \(G(\mathbb A_F)^1\),
the common kernel of the rational character norms, is assumed to be
right invariant.

Let \(A_i\) be the image in \(G(\mathbb A_F)\) of the positive real
coordinates of \(T\), embedded diagonally at the infinite places. The
quotient is \(A_iG(F)\backslash G(\mathbb A_F)\). Its measure
`positiveRationalQuotientHaarMeasure` is the pushforward of the Library's
Haar quotient measure on \(G(F)\backslash G(\mathbb A_F)^1\) along the
inclusion-induced homeomorphism. The integrated operator \(R(f)\) uses
the original quotient right translations and `Measure.haar` on the
full adelic group for the integral. Fix a closed matrix embedding
\(\rho\) of positive size and write \(H_\rho\) for the Library's
`RepresentationGrowth.adelicHeight`.

There is a natural number \(d\) independent of the weight. For each
compactly supported continuous weight \(f\) on the full adelic group,
with its Haar integrability witness, there is a constant \(B_f\ge 0\).
For every input class \(\phi\) in the quotient \(L^2\), there is a
continuous function \(\psi\) equal almost everywhere to the integrated
output \(R(f)\phi\) for the quotient measure and satisfying
\[
|\psi([x])|\le B_f H_\rho(x)^d\|\phi\|_2
\qquad\text{for every }x\in G(\mathbb A_F).
\]
The height is evaluated at the displayed representative \(x\). The
estimate covers the whole quotient \(L^2\). In the cuspidal application,
the later bound (9.13) of Getz–Hahn is uniform in \(x\). Their Lemma
9.3.3 combines such uniform evaluation bounds on a closed invariant
subspace with finite quotient volume and smooth convolution
factorization to prove trace class (printed pp. 247–248, PDF pp. 259–260).

This is a derived continuous-weight form of the function-value estimate
in Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series*
(1995), I.2.4 Lemma (a)(i) and I.2.5 Lemma (b), printed pp. 25–27
(PDF pp. 8–10 in the chapter file
`05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`).
The source takes smooth weights and \(L^2\) modulo the centre with a
unitary central character. The present estimate concerns continuous
weights and the original positive rational quotient measure.
The Library's height is a fixed positive multiple of the source norm for
the chosen embedding. The continuous representative estimate uses
`tsupport f * (tsupport f)⁻¹` and the subgroup measure on the conjugate of that
compact set. In positive-times-principal coordinates the first projection
of the conjugate stays in a fixed compact set and the second is bounded
by the rational point count.

For connected reductive \(G\) and a split component \(i\), the Library's
`RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup` identifies
\(A_i\) with the canonical subgroup. This subgroup is \(A_G\) of
Getz–Hahn, *An Introduction to Automorphic Representations* (2024), (2.20),
the image of the identity component of the real points of the greatest
\(\mathbb Q\)-split torus in \(\operatorname{Res}_{F/\mathbb Q} Z_G\).
In this setting the quotient and the inclusion-induced normalization
above use (2.19)–(2.22) and Lemma 2.6.2, printed pp. 68–69
(PDF pp. 85–86).
