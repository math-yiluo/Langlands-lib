# Product estimates for the actual rectangular gauge

This internal module defines `rectangularDiagonalPoint`, the lower rectangular
matrix chart with a diagonal leading block, transported to actual adelic
points. Its only difference from the published `rectangularPoint` formula is
an explicit rank reindexing. `lintegral_lowerBlock_rank_congr` proves the
integral transport along any equality of rectangle ranks by equality
elimination. `rectangularLIntegral_diagonal_add` then identifies its integral
with the published actual rectangular integral when `r=t+1+d`.

For every simple-root gauge of exponent `τ`, the module constructs one
rank-one Schwartz–Bruhat function whose product in the original block roots
and all rectangular entries bounds
`Ξ(rectangularDiagonalPoint(b,x)) * |det b|^τ`. All hypotheses of the gauge
remain unchanged, including its actual standard-compact invariance.

The proof applies the published compact Iwasawa theorem to the singleton
lower unipotent at `x`. It transfers this factorization to every leading
diagonal by the preceding diagonal-correction identity. The gauge's left
unipotent and right standard-compact invariances identify its value with its
diagonal profile. Determinant norm is unchanged by the unitriangular and
standard-compact factors. The standard last row gives last diagonal norm at
most one, so `normalized_gauge_weight_le_roots` bounds the normalized scalar
weight by the positive actual-root powers. The previously proved product
majorant bounds those powers times the Schwartz profile. Passing through
`ENNReal.ofReal` gives the asserted pointwise estimate.

The final theorem integrates this bound with the actual rectangle measure.
The rectangle product integral is a finite scalar `M`, independent of the
leading diagonal and Mellin exponent. Pulling out the finite scalar weights
and using `|det b|^τ * |det b|^(σ-τ) = |det b|^σ` yields a bound by
`M * (product of leading-root Schwartz norms) * |det b|^(σ-τ)`.
This proof works with zero rectangle rows as well. Torus and Whittaker
quotient integration are not claimed in this module.
