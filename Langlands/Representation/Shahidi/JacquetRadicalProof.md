# Boundary kernel and radical covariance of the scalar Jacquet integral

Author: Worker 643.

This internal proof unit targets the published proposition
`Langlands.Shahidi.JacquetRadicalCovarianceStatement` in
`JacquetRadicalStatement`. Its provenance is the literal published rectangular
subgroup, character and scalar Jacquet-integrand definitions, together with
ordinary integration against a measure invariant under right addition.
It asserts no section-existence or full upper-unipotent result.

The boundary calculation transports the superdiagonal sum through
`Shahidi.swapRank`. This arithmetic reindexing preserves numerical matrix
positions and differs from the block Weyl permutation. A finite equivalence
transports the index set, and equality of the `castSucc` and `succ` indices
reduces to their numerical values. The existing
`RankinSelberg.TwoBlockJacquet.sum_superdiagonal_upper` then identifies the
sum with `x(last n,0)`. Applying the actual character yields its positive
corner formula. The published inverse-kernel identity and the additive
character's negative-input identity yield the negative corner for the kernel.

Multiplicativity of `intertwiningCharacter`, nonzero values in complex units,
and inverse cancellation show
`kernel(x) = character(y) * kernel(x+y)`. The actual matrix identity
`intertwiningUnipotent(x+y) = intertwiningUnipotent(x) *
intertwiningUnipotent(y)` then proves pointwise right-translation covariance
of `jacquetIntegrand`.

For a supplied right-addition-invariant measure, Mathlib's
`Integrable.comp_add_right` preserves integrability under the coordinate
translation, and multiplication by a constant preserves it again. The
ordinary integral factors out the character, while
`integral_add_right_eq_self` removes the coordinate translation. The integral
equality in fact holds for all functions with the totalized Bochner-integral
convention; the target only asks for it on the integrable domain and separately
requires integrability of the translated function.

The final theorem `jacquetRadicalCovariance` assembles the two closed statements
with independent field and coefficient universes. It supplies only the exchanged
rectangular radical part of the JPSS construction. The two-block Whittaker
extension theorem, compact cell sections, covariance under the remaining
upper-unipotent factors, and Fourier surjectivity remain separate obligations.
