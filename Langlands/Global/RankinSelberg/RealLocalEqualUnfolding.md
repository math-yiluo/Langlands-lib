# Real equal-rank unfolding of a Godement quotient coefficient

**Source.** Hervé Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §8.2, pp. 54–55, from the unipotent averaging through equation (8.1), registered as `jacquet-2009-archimedean-rankin-selberg`. This is an internal conditional form of (8.1). It starts with the Library's actual recursive quotient kernel and makes its measure normalization explicit; it does not use a parameter chamber to justify the changes of variables.

## Statement and normalization

Write \(m=t+1\), \(n=t+2\), \(G_j=\mathrm{GL}_j(\mathbb R)\), and let \(N_j\) be the upper unipotent subgroup. Let \(D\) and \(D'\) be compatible real quotient data for \(N_m\backslash G_m\) and \(N_n\backslash G_n\). The statement takes a positive scale \(c\) with `D'.unipotentHaar = c • upperStepHaar (t+1) b`, where the latter is the product of the self-dual entry measures for the nonzero additive parameter \(b\). This scale can be obtained from the first two conjuncts after the existential in `realGodementColumnQuotient` at rank index `t+1`. The theorem keeps it explicit so the same comparison can be used after reflection.

Let \(W\) and \(V\) be functions on \(G_m\) and \(G_n\) satisfying `KernelWhittakerLaw b W` and `KernelWhittakerLaw (-b) V`, respectively. In this API the law at \(b\) uses the standard character with additive parameter \(-b\). Given a Schwartz rectangle test \(\Phi\) on \(m\)-by-\(n\) matrices, a last-row function \(\phi\), and real character data \(d\), define the square test

\[
  \Psi(A)=\Phi(A_{\mathrm{first}\ m\ \mathrm{rows}})\,\phi(A_{\mathrm{last}\ \mathrm{row}}).
\]

Let \(C_d=d(-1)^m\), with \(d\) evaluated via its character. `equalRecursiveCoefficient` is \(C_d\) times the integral of `quotientKernel b Φ W hW d` at \(w_n g\) against \(D\)'s quotient measure. `equalUnfoldedKernel` uses the canonical Iwasawa representative \(h\) of the lower quotient class and is the function

\[
  (q,g)\longmapsto
  \Psi(g)\,V(\operatorname{diag}(h,1)g)\,d(\det g)|\det g|^{s+m/2}\,
  W(h)|\det h|^{s-1/2}.
\]

`RealLocalEqualUnfoldingStatement` at `t` assumes this function is jointly integrable for the product of \(D\)'s quotient measure and \(D'\)'s ambient group Haar. It concludes that the integrand of `realEqualIntegral` with the recursive coefficient, \(V\), and \(\phi\) is integrable on the larger quotient and that \(c\) times that equal-rank integral is the joint integral of the unfolded kernel. The pair includes the proof `realLocalEqualUnfolding`. The row function \(\phi\) needs no separate measurability or Schwartz premise for this conditional identity.

## Implemented proof

1. For the orbit of \(g\), substitute \(\operatorname{diag}(h,1)^{-1}u g\) into the unfolded kernel. The last row is unchanged by the unipotent and the padding. The first \(m\) rows of \(u g\) are the published step rectangle times \(w_n g\), with the left reversal \(w_m\). The determinant of \(u\) is one. The shift in the lower determinant power leaves exponent \(n/2\) on \(h^{-1}\), and the character of \(V\) at \(u\) gives precisely the phase of the step chart. The two Weyl determinants contribute \(C_d\), whose square is one; this is why the normalization in `equalRecursiveCoefficient` produces the stated kernel without a residual sign on the primal side. The measure-preserving step chart then gives the orbit average as the corresponding quotient-kernel value times the factors at \(g\).
2. On the product of the lower quotient and the larger group, translating the larger group coordinate on the left by \(\operatorname{diag}(h,1)^{-1}\) is measure preserving. The section is continuous, and each fiber translation preserves left Haar. Compose this change of variables with the published real Iwasawa quotient product map and with two product-coordinate rearrangements; the resulting chart has the larger quotient as its outer coordinate, followed by the lower quotient and the larger unipotent group.
3. Inside the innermost Haar integral, the chart's canonical larger representative can be replaced by the representative `q'.out` used by `equalIntegrand`. They differ by the left unipotent coordinate of `q'.out`, so the replacement is a right translation in the integrating subgroup. This use of right invariance does not require the map `q' ↦ q'.out` to be measurable. Use the supplied Haar scale and the pointwise orbit computation. Fubini twice on the transported integrable function gives the scaled equal-rank integrand almost everywhere and identifies the two integrals. Positivity of the scale implies integrability of the unscaled equal-rank integrand.

## Scope

The proof does not establish joint integrability on a half-plane, compare the recursive coefficient with the full uniform Whittaker model, unfold the dual integral, or furnish a finite expansion. In particular it does not prove `RealLocalUniformPositiveEqualContinuationStatement`.
