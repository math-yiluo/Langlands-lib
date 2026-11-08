# Holomorphy of the actual finite Hecke Mellin series

This internal derived unit concerns the actual finite divisor series
`finiteMellin`. Its logarithmic coefficient slope is the sum over the divisor
support of minus the integer valuation times the logarithm of the actual
residue cardinality. The local shell exponential formula multiplies to give
the corresponding divisor coefficient formula, including coefficients that
vanish. Differentiating this exponential gives its slope times its value.

The Euler test at an unramified place is supported on nonnegative integer
shells; at a ramified place only the zeroth shell survives. The norm of the
spectral variable decreases when the real part increases because the residue
cardinality exceeds one. Consequently every shell norm and every divisor
coefficient norm has this monotonicity.

If the coefficient norms are summable at a real parameter `t`, this
monotonicity supplies a summable bound throughout `t ≤ re(s)`. The
Weierstrass bound for unordered sums therefore proves uniform convergence
of the finite partial sums to the actual `finiteMellin χ` on that entire
closed half-plane. Each coefficient is entire by the exponential formula.
The locally uniform limit theorem consequently proves holomorphy on
`t < re(s)`. Its derivative version gives a `HasSum` statement for the series
of logarithmic slopes times the actual coefficients, with sum equal to
`deriv (finiteMellin χ) s`. This derivative statement asserts convergence,
without asserting an additional absolute-convergence estimate.

`exists_finiteMellin_analytic_halfPlane` supplies such a real bound for
every actual Hecke character. The proof takes a real parameter strictly
inside the already proved absolute-convergence half-plane, and increases
it if necessary to reach the nonzero Euler-product half-plane. The
`HasProd` for the actual divisor sum and the `HasProd` for the previously
proved nonzero local-factor product have identical local factors;
uniqueness of the limit proves that `finiteMellin χ s` is nonzero. The
result gives uniform convergence on the chosen closed half-plane,
holomorphy of the sum and its reciprocal on the open half-plane, and
pointwise absolute convergence, the exact Euler-product identity and
nonvanishing there.

The common analytic half-plane theorem retains every quantifier over the
number field, actual Hecke character, global nontrivial unitary additive
character trivial on the diagonal, supplied finite components, supplied
self-dual Haar measures, and nonzero real and complex component scales.
The conductor-support and finite-Mellin theorems give one finite
exceptional set, independent of the spectral parameter. Taking the
maximum of their convergence bound and the analytic bounds for `χ` and
`χ⁻¹` gives holomorphy of both actual finite sums. On this common half-plane,
the Fourier divisor sum is exactly
`finiteGlobalEpsilon χ ψf μ (1 - s) * finiteMellin χ⁻¹ s`.
The finite epsilon product is entire and nonzero for the supplied data.
Composition with `1 - s`, multiplication, and the established identity
therefore prove holomorphy and nonvanishing of the Fourier sum, as well as
holomorphy of its reciprocal. Both finite sums are nonzero there, and the
zeroth Fourier weight and epsilon factors equal one outside the same
finite set for all complex parameters.

This is an internal analytic consequence of the actual shell definitions,
the existing coefficient and Euler-product convergence results, and the
finite epsilon-product theorems. The proof uses Mathlib's
`tendstoUniformlyOn_tsum`,
`Complex.differentiableOn_tsum_of_summable_norm`, and
`Complex.hasSum_deriv_of_summable_norm`. The included supporting pairs are
unchanged; Worker 1798 supplied their lattice arithmetic. This unit proves
only analytic properties on a right half-plane. Analytic continuation to
the whole plane and the global functional equation remain separate
obligations.
