# Center kernels, rational fibres, and reduction to affine charts

This module develops reductions for the unchanged
`Langlands.Analytic.SchemeAnalytification.AnalytificationCenterStatement`.
It does not prove that entire proposition; `AnalytificationCenterProof`
combines these reductions with the remaining inputs to prove it. The statements that take
seminorm injectivity, affine surjectivity, or chart range identities as
arguments are explicit conditional reductions.

The affine rational-point seminorm formula follows by evaluating the
published chart character on an element of the coordinate algebra. It
reproduces the short calculation of `pointSeminorm_analyticPoint_apply` in the
rational-point comparison `AffineAnalytificationRationalPointsProof`. Its
kernel is the algebraic point's kernel. If a second
point has that center, the difference between an element and its scalar
value under the rational point has seminorm zero. Applying the triangle
inequality in both directions shows equality of the two seminorms. Seminorm
injectivity then gives equality of the analytic points.

For schemes the module identifies the center of a local rational point by
the spectrum map of its coordinate character, then composes with the affine
open inclusion. The chosen affine factorization yields the global
rational-center formula. Affine center surjectivity gives scheme center
surjectivity by taking an affine neighborhood of any point. The singleton
rational fibre is reduced to the affine result by the chart range identity
and injectivity of the affine open's algebraic map into the scheme.

These are derived arguments implementing the rational-center and rational
fibre consequences explained in the target's published Markdown. The
sources and conventions are retained there: Berkovich (1990), Theorem
3.4.1(i), proof steps (2)–(3), and Remark 3.4.2, and Conrad–Temkin (2009),
§4.1. No new claim is attributed to a numbered source statement.
