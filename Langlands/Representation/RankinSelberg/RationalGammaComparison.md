# Rational gamma comparison from cross identities

This module supplies derived algebra for the existing `GammaFunctionalEquation`
relation. It is an internal construction from rational functions, the published
reflection `RationalReflection.subst`, and the evaluation results in
`RationalEvaluation`. It is not a new assertion from the Rankin–Selberg literature.

Write \(\rho_\delta\) for substitution \(X\mapsto\delta/X\).
The definition `gammaRatio δ ζ e R Rdual` is
\[
  \frac{\rho_\delta(R_{\mathrm{dual}})}
       {C(\zeta^e)R}.
\]
Here both \(\delta\) and \(\zeta\) are nonzero complex units. The quotient is
defined for all rational arguments using field division. Its useful comparison
property requires a nonzero original anchor, and its nonvanishing requires a
nonzero dual anchor.

`gammaFunctionalEquation_of_rational_identity` evaluates
\(\rho_\delta(R_{\mathrm{dual}})=C(\zeta^e)GR\) when \(q>1\) and
\(\delta=q^{-1}\). The published identity for the spectral point gives
\(\delta/q^{-s}=q^{-(1-s)}\). The dual denominator hypothesis justifies reflected
evaluation. The original and gamma denominator hypotheses justify evaluating
their product. Constants are regular everywhere. Thus the conclusion is the
existing gamma equation on its entire stated domain, with all three denominator
conditions. No condition on the anchor used to construct a quotient is added
to that domain. The converse is imported from
`GammaNormalization.rational_identity_of_gammaFunctionalEquation`, giving the
displayed equivalence.

`rational_cross_of_spectral_cross` accepts a cross-multiplication equality of
four evaluations outside a specified finite set of spectral points, whenever
all four original denominators are nonzero. The implementation removes the
finite preimage of that exceptional set and the finite real-parameter zero
sets of the four denominators. Infinitely many distinct real spectral points
remain. Both reflected products are regular there; evaluation of products and
reflection gives equality. The published rational-function identity lemma on
an infinite set then proves the rational cross identity. No evaluation at a
pole is used.

`gammaRatio_identity` cancels a nonzero original anchor in one rational cross
identity. `exists_gammaFunctionalEquation_of_cross` applies this to arbitrary
families \(R_i,D_i\) indexed by any type. Its hypotheses are
\[
 (\exists i,\ R_i\ne0),\qquad(\exists j,\ D_j\ne0),\qquad
 \rho_\delta(D_i)R_j=\rho_\delta(D_j)R_i\quad\text{for all }i,j.
\]
The two nonzero witnesses need not have the same index. The cross identity at
these witnesses and injectivity of reflection force the dual value at the
chosen original anchor to be nonzero. Consequently the quotient is nonzero,
and the same quotient gives the gamma equation for every index.

These results do not supply any of their rational families, nonzero witnesses,
or cross identities for actual integrals. In particular, they establish neither
rational continuation nor bilinear or trilinear uniqueness, and they do not
prove the unequal-rank block-zero gamma existence statement. Those analytic and
representation-theoretic inputs remain separate obligations.
