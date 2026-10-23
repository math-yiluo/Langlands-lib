# Finite averages for the normalized compact Haar variable

`Langlands.RankinSelberg.EqualRankNormalizedCompactIntegrationStatement F T n`
specializes compact averaging to the actual integral subgroup and Haar measure
used in the equal-rank JPSS construction. Here `F` is any specified p-adic field,
`T` is its supplied topological data, and the matrix rank is `n+1`, including
rank one. The field and two representation universes remain independent.

Install the topology, valuation and local-field structures supplied by `T`.
Let

\[
K=\mathrm{GL}_{n+1}(\mathcal O_F),\qquad
dk=\left.\texttt{generalLinearHaar}\right|_K .
\]

In Lean, `K` is the actual subgroup
`Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n`,
and `dk` is the restriction of `generalLinearHaar F.Carrier n` to that subgroup
as a measure on the ambient general linear group with its Borel structure.
The previously published measure has `K` of mass one.

For any smooth representations, their specified standard and inverse-character
functionals, coefficient-model vectors `f,f'`, and Schwartz–Bruhat row test `Φ`,
the proposition supplies finitely many `k_i ∈ K` and nonnegative real numbers
`c_i` with `∑ c_i = 1`. The family is chosen before the arbitrary matrix `g`
and spectral parameter `s`. For all `g,s`, the actual function

\[
H_{g,s}(k)=f(gk)f'(gk)\Phi(e_{n+1}gk)|\det(gk)|_F^s
\]

is integrable for `dk` and satisfies

\[
\int H_{g,s}\,dk=\sum_i c_i H_{g,s}(k_i),\qquad
\int |H_{g,s}|\,dk=\sum_i c_i |H_{g,s}(k_i)|.
\]

The second formula uses the nonnegative extended integral and the extended
norm in Lean. The absolute value is exactly `normalizedAbsoluteValue T`,
the residue-cardinality normalization from the analytic statement. There are
no assumptions of irreducibility, admissibility, nonzero functionals,
or restrictions on `s`. Only the compact variable is integrated.

This is a derived specialization of `EqualRankCompactIntegrationStatement`,
with the following additional normalization and measure identifications.
The conductor construction proves that `K` is compact and open. Both an
integral invertible matrix and its inverse have integral determinants.
Their normalized absolute values are at most one and their product is one,
so each determinant absolute value is one. Pull the ambient Haar measure
back to the measurable subtype `K`; this finite measure has total mass one.
The general compact statement applies on that subtype. Pushing its measure
forward by the subtype inclusion gives the actual ambient restriction `dk`,
which transfers integrability and both integral formulas. These facts are
part of the intended derivation, not additional hypotheses of this proposition.

The source motivation is Jacquet–Piatetski-Shapiro–Shalika,
*Rankin–Selberg Convolutions* (1983), proof of Theorem 2.7, printed p. 391,
the paragraph preceding display (3) and display (3). That passage combines
Iwasawa integration with simultaneous compact finiteness of the coefficient
functions and the test function. This proposition isolates the compact average
with the Library's fixed mass-one normalization. It does not state the
Iwasawa quotient measure identity or any noncompact convergence, rationality,
common-denominator, or normalized-generator conclusion. It is a proposition
definition; its proof is a separate contribution.

Source: `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
printed p. 391, proof of Theorem 2.7, paragraph before (3) and display (3).
