# Actual Weil charts from the invariant coefficient algebra

This internal derived module constructs the actual Weil group of the invariant
coefficient algebra over the affine base and actual local group-scheme
isomorphisms with the supplied group.

`WeilCoefficientTensor.equiv` is the actual coefficient tensor decomposition
on every algebra over a chart ring. Its pure-tensor formula evaluates the
local coefficient decomposition on `1 ⊗ c`, then multiplies by the test scalar.

`invariantFinite`, `invariantProjective` and `invariantEtale` use the proved
coaction descent properties. `weilGroup` pulls its Weil group from the spectrum
of the base's global-section ring back along the canonical affine isomorphism.
`specWeilChart` composes the actual Weil base-change isomorphism, the local
coefficient algebra equivalence, and the split-coefficient Weil isomorphism.
`specWeilChart_hom_points` proves on every relative test that the spectrum
chart applies the unit map of this actual coefficient tensor decomposition.
Its proof composes the published point formulas of Weil base change, algebra
congruence, and splitting for a coordinate-function algebra.

`weilChart` normalizes this chart back to the actual affine chart scheme using
the canonical pullback comparison and affine isomorphism naturality.
`localWeilIso` compares the supplied actual split chart with this actual Weil
chart.

The hypotheses are the finite flat jointly surjective affine permutation atlas;
coordinate ranks may vary or vanish, and zero rings and empty bases are allowed.
This module does not yet prove compatibility of the local group isomorphisms or
descend them to a global Weil comparison.
