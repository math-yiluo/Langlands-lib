# Entire strict-rank determinant-slice families

This internal unit proves entire dependence of the literal determinant-slice
coefficients `strictSliceCoefficient`, at every complementary rectangular row.
It works over a canonical p-adic field in universe `uF`, with an independent
representation carrier in universe `uV`. The actual larger rank is `r + 1`, the
smaller rank is `n + 1`, and `r = n + (j + k + 1)`.

`StrictRankEntireSliceData` is the proposition that each such coefficient is an
entire function of the complex family parameter. It concerns the actual supplied
quotient measure and actual product of the supplied scalar additive Haar measure.
It makes no whole-integral convergence or factor-existence assertion.

## Restricted integral identity

`strictSliceCoefficient_eq_restrictedIntegral` identifies a literal coefficient
with `unequalRankIntegralAt` at spectral parameter zero and quotient measure
restricted to its determinant slice. It applies `strictIntegral_eq` to that
restricted measure. The imported measurable-space equality transport changes
neither the integrand nor the measure's mass.

## Zero rows

`strictZeroRowSlice_entire` assumes a smooth larger representation, a fixed
coefficient in its Whittaker model, and an inverse Whittaker family whose point
evaluations are entire and whose right invariance has one common open subgroup.
The quotient measure is finite on compact sets. The functional need not be
nonzero in this zero-row lemma.

The proof intersects the family's right level, the fixed coefficient's level
pulled back along `appendIdentity`, and the integral general linear subgroup.
This gives a compact open subgroup. Its determinant has normalized absolute
value one, so both the zero-parameter determinant weight and the entire averaged
integrand are invariant under this subgroup.

The actual zero-row average is the product of the fixed diagonal coefficient,
the inverse-family point value, and the fixed determinant weight, multiplied by
the actual real mass of the zero-row rectangle measure. No additional measure
normalization is assumed. `diagonalWhittaker_slice_hasCompactSupport` gives
compact support on each determinant slice for the fixed diagonal coefficient.
The compact right-orbit cover and finite-evaluation integral theorem from
`CorankSliceFiniteEvaluation` express the slice integral as a fixed finite sum of
point evaluations with fixed orbit masses. Each summand is entire by the given
pointwise hypothesis; hence so is the coefficient.

## General rectangular rows

`strictSlices_entire` assumes full Whittaker type of the larger representation
and a nonzero fixed functional, in addition to the same common-level and
pointwise-entire hypotheses on the inverse family. Full type is not replaced by
irreducibility. These assumptions supply the uniform rectangular support in the
published `unequalRankCompactSupport` theorem.

The proof inducts on `j`, generalizing the complementary column count `k` and
the fixed coefficient. At a successor row,
`exists_adjacent_block_integral_coefficient` integrates out one row and produces
a coefficient in the same original model. Its equality concerns the actual
inner rectangular averages at every smaller group element. Both literal slice
coefficients are rewritten as restricted integrals using the first lemma, then
`unequalRankIntegralAt_eq_outer` and the inner-average equality identify them at
every complex family parameter. The dimension equality preserves the fixed
determinant weight. The induction hypothesis applies to the resulting
coefficient at row `j` and column count `k + 1`.

This coefficient identity is proved directly under each restricted measure.
No claim of convergence is inferred from an equality of total Bochner integrals.
The result supplies neither rational continuation nor gamma or L certificates;
those require separate analytic assembly.

## Provenance

This is an internal deduction from the published diagonal-support, finite
right-orbit evaluation, compact rectangular support, same-model block
integration and exact measure-transport results named above. It introduces no
new literature translation and no premise asserting the desired analytic base.
