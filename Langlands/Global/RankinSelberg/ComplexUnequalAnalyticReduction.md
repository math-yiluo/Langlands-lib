# Analytic reduction for the complex unequal-rank functional equation

`ComplexUnequalAnalyticReductionStatement` expresses an implication to
`ComplexLocalUnequalFunctionalEquationStatement`. It uses the ordinary quotient integral and
the dual rectangular integral in the published statement, for `GL_(r+1)(ℂ)` and
`GL_(t+1)(ℂ)` with `t < r`. It has two open premises on pairs of values `B f` and `B' f'`
of the specified Whittaker intertwiners for `ψ_a` and `ψ_(-a)`.

- `ComplexUnequalIntertwinerConvergenceStatement` gives absolute convergence on a right
  half-plane, with the quotient measure for the ordinary kernel and the product of the
  quotient and rectangular measures for the dual kernel.
- `ComplexUnequalNormalizedIntertwinerEquationStatement` gives entire functions `N` and `Nd`
  that agree on a right half-plane with the corresponding integrals multiplied by the
  denominators of the Library's ordinary and dual reciprocal Gamma products. It asserts
  `Nd(1 − s) = complexCentralSign d' ^ r · ε(s) · N(s)` for all `s`, with the exact sign and
  epsilon factor from the target. Each half-plane threshold may depend on the input pair.

`complexUnequalAnalyticReduction` proves the implication. The log of the squared absolute
value of the determinant is measurable on the quotient because the determinant descends
continuously through the projection. The dependence of both kernels on `s` is exponential
in this real log. At a point `z` inside the half-plane, Lean chooses a real radius `δ` small
enough that `z ± 2δ` lie in the half-plane. The derivative of the kernel on the ball of
radius `δ` is dominated by the sum of the norms of the integrable kernels at `z + 2δ`,
`z − 2δ`, and twice the norm at `z`, divided by `δ`. The proof applies differentiation
under the integral. Fubini identifies the dual product integral with the iterated integral
on this half-plane. The rectangular measure is sigma finite by its construction from
additive Haar measure, and the compatible quotient measure is regular on a sigma compact
quotient.

Pairs of kernels with both properties form a complex submodule. The proof uses linearity
of both integrals in the kernels, taking intersections of right
half-planes when adding witnesses. The ordinary and dual kernels are bilinear in the two
Whittaker functions, so submodule preimages in each variable extend the premises through
the suprema of the intertwiner ranges. The poles of the finite products of shifted complex
Gamma factors have real parts bounded above. On a common smaller right half-plane, dividing
the entire witnesses by their denominators gives the original integrals. These quotients
are meromorphic on the complex plane. Multiplying the normalized equation by the two
reciprocal denominators gives the crossed identity of the target for the chosen representatives.

This is an internal reduction of the Library proposition. The input clauses correspond
to the convergence and normalized continuation in Jacquet's Theorem 2.1 for integrals
(2.4)–(2.6). The sign and Fourier convention in the second clause are those of the
Library target. For the larger rank gaps, compare the sign in Jacquet's proof after
(10.10) with the display in Theorem 2.1, and use the negative Fourier transform in
Jacquet's conventions. [Jacquet, *Archimedean Rankin–Selberg integrals*, pp. 3–6, 76 and 110–111](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
