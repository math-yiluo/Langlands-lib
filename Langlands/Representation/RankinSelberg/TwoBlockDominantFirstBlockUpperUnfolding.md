# The actual global upper first-block unfolding

This module completes the upper quotient specialization of the neighboring
global-analysis helper. It is derived infrastructure for the first-block
calculation in Jacquet, Piatetski-Shapiro and Shalika (1983), §4.9, printed
pp.416–418, and its strictly dominant extension in §4.10(2), printed p.419.
The source illustrates the latter with `k=0`; the arbitrary complementary
dimensions and the explicit product convergence statements here are derived
refinements using the published exact quotient towers.

Write `a=m 0+1`, `b=m 1+1`, and `c=j+k+1`, so `a+b=t+1`.
Both block sizes are positive, while `j,k` may be zero. The field has its
canonical p-adic topology, valuation and Borel structures. Field, large test
carrier and block carrier universes remain independent. The scalar additive
Haar measure `ν` is supplied, with all rectangular measures its actual finite
products. No supplied functional is assumed nonzero.

`firstBlockUpperQuotientAverage` is a function on the actual lower mixed
quotient. First integrate the original section integrand over the external
`j × (t+1)` rectangle at determinant exponent `-c/2`. Apply the actual
first-block quotient average on small determinant slice `d`, then the actual
lower radical average with the supplied `b × a` product measure. Both averages
descend their invariant integrals, so the definition chooses no quotient
representative. Its definition alone asserts no convergence.

`firstBlockUpperQuotientAverage_analysis` assumes a large test representation
of full Whittaker type, smoothness of the first block, and ordinary absolute
Jacquet convergence of the supplied section for an arbitrary supplied
`a × b` additive Haar measure. The large standard, block, small standard,
mixed and lower mixed quotient measures must be compatible with the exact
specified subgroup Haar measures. The block and small quotient measures are
sigma-finite. The conclusion supplies:

- Measurability and integrability of the quotient average on the lower mixed
  determinant slice zero.
- For almost every point of that slice and every representative `g`, genuine
  integrability of the actual row average jointly in the radical matrix `Z`,
  the small quotient `q` on slice `d`, and the remaining `j × b` columns `Y`.
- At each such point, equality of the quotient average with
  `firstBlockUpperGlobalAverage`, the actual integral over `Y` of
  `firstBlockUpperCoefficient`.
- An exact global integral formula: the lower mixed integral is the radical
  integral-cube mass times the original block-quotient integral of the
  external rectangle average on block determinant slice `d`.

The proof uses the finite rectangular expansion to obtain original rectangle
integrability at every actual fiber and continuity of its signed average.
The first-block quotient unfolding makes its average `B` measurable and
integrable on the mixed zero slice. The radical kernel then proves
measurability of the second average; the radical integration theorem supplies
its integrability and integral formula.

Separately, the original real raw-norm profile is measurable and integrable
on the block determinant slice by the existing fiber theorem. The composed
kernel theorem transfers this original profile to the actual `Z × q` product
almost everywhere on the lower mixed zero slice. The joint product control
theorem applies using the pointwise original rectangle convergence,
continuity of the actual large model function, and first-block smoothness.
It proves triple-product integrability and the signed Fubini formula before
the actual representative formulas for the two quotient averages identify
the result. The global integral formula follows from the two exact towers.
Thus no global raw-profile premise is added to this specialization.

`rectangular_integerCube_mass_swap` proves equality of the integral-cube
masses for the `a × b` and `b × a` products of the same scalar Haar measure.
Expressing each cube as two finite product sets and applying the product
measure formula gives powers of the same scalar mass; commutativity of
natural multiplication identifies their exponents. This retains the supplied
normalization, including at zero rectangle dimensions in this lemma.

`firstBlockUpperQuotientAverage_integral_eq_large` specializes the ordinary
Jacquet measure to the supplied scalar `a × b` product. It assumes an actual
inverse-character Whittaker function whose values are that ordinary Jacquet
integral, as well as its absolute convergence. For the compatible measures
above, with the large standard quotient also sigma-finite, the lower mixed
integral of the upper quotient average is exactly
the original large JPSS iterated integral on determinant slice `d`, at
spectral parameter zero and with the supplied external rectangle measure.
The earlier radical unfolding gives the latter integral as the `a × b`
cube mass times the block-quotient integral. The analysis theorem gives the
former as its `b × a` cube mass times the same integral. The mass-swap lemma
identifies these constants, leaving no rescaling.

This module implements the upper analytic disintegration and its exact
normalization. It does not identify a lower reflected coefficient, construct
common epsilon witnesses, or prove the finite Laurent identity. The final
closed proposition still requires those steps and its unconditional lower
convergence conclusions. Its target and imports are unchanged.
