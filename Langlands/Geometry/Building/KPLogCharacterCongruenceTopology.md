# Open logarithmic character congruence subgroups

Let `k` be an ultrametric normed field and `G` a group scheme over `k` whose
underlying scheme is affine. Assume that its actual rational character module
is finitely generated over the integers. For a positive real scale `c`, the
actual-character congruence subgroup defined using the normalized negative
logarithm of the norm valuation is open at every nonnegative real depth.
The point topology is exactly `rationalPointTopology k G.X`, and field units
carry the induced units topology.

The proof applies `isOpen_characterCongruence` to the scalar openness theorem
`isOpen_addValuationUnitFiltration_log` from the paired supporting module
`Langlands.LocalField.LogCongruenceTopology`. Thus a finite generating family
of characters reduces the assertion to finitely many inverse images of open
scalar subgroups under continuous character evaluations.
`logCharacterCongruenceOpenSubgroup` bundles the resulting subgroup and its
openness; its underlying subgroup is exactly the existing
`characterCongruence` at this logarithmic valuation.

This is derived infrastructure using Mathlib ultrametric topology and the
published rational-point character continuity API. No completeness,
discreteness or split-torus hypothesis is needed for this openness assertion.
It does not identify the zero group with a torus Iwahori subgroup or construct
the centralizer filtration required by the host existence statement.
