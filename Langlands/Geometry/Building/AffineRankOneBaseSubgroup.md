# The actual filtered rank-one base cell is a subgroup

This derived module defines `affineRankOneBaseSubgroup` as the subgroup
supremum of the actual weak positive affine root group, the actual strict
negative affine root group, and the mapped supplied centralizer-zero
subgroup. Under apartment axioms, the explicit cover-image comparison and
actual rank-one pair existence, its carrier equals the original
`affineRankOneBaseCell` from `AffineRankOneTwoCellStatement` whenever the
functional has the specified root derivative. No filtration jump is needed.
The cover comparison and pair existence are intermediate premises, not
additional hypotheses on the final two-cell target.

For the exchange of a weak positive element and a strict negative element,
identity cases have immediate factorizations. Choose any apartment point.
Nonidentity elements have finite valuation by V1. The positive depth is
at least the functional value, while the negative depth is strictly greater
than its negative; their sum is positive. The structured actual
centralizer-zero factorization from `RankOneZeroFactorization` gives a
negative factor of at least the original negative depth and a positive
factor of at least the original positive depth. The published weak and
strict affine-root membership criteria put them back in the required
original subgroups.

Worker 1612's actual centralizer-zero normalization theorems show that the
mapped centralizer zero normalizes both factors. The internal generic
three-factor subgroup criterion then identifies the carrier of their
supremum with the literal strict-negative, centralizer-zero, weak-positive
set product. This is the subgroup step for the base cell in the proof of
KP Lemma 7.1.5(3), derived from the imported factorization and normalization
results. It neither proves the final two-cell union nor discharges the
cover comparison or pair existence.
