# Comparison of right-invariant measures on actual left quotients

This internal helper is derived from the published real quotient averaging,
positive lifting, compact translation and topology APIs, together with
Mathlib's real Riesz representation and regular Haar uniqueness theorems.
It is intended to support measure comparison on the actual lower-block
orbit. It asserts no geometry or measure identity for that orbit.

The ambient group is any locally compact Hausdorff topological group with
its Borel measurable structure. The subgroup is closed and has a supplied
regular Haar measure that is also right invariant, with its Borel structure.
The quotient is the published `LeftQuotient H`, whose points are the left
cosets `H g`, with the quotient topology and its Borel structure.

`quotientMeasureLift` associates a group measure to any quotient measure
finite on compact sets. Apply the published positive real averaging
operator to a compactly supported continuous real function on the group,
then integrate that average against the quotient measure. This positive
linear functional has a regular Riesz measure on the group.
`integral_quotientMeasureLift` is its integral representation formula.

`quotientMeasureLift_rightInvariant` uses the actual averaging translation
formula to show that a quotient measure invariant under every right
translation has a right-invariant lift. It tests the pushed-forward group
measure on compactly supported continuous real functions and uses quotient
invariance. `quotientMeasureLift_ne_zero` uses the published positive lifting
theorem: a compact quotient test with nonzero integral lifts to a compact
group test with the same integral.

`exists_pos_smul_eq_of_rightInvariant_quotient` compares two nonzero regular
quotient measures, each invariant under every right translation. Inversion
sends their nonzero regular right-invariant group lifts to nonzero regular
left Haar measures. Mathlib's Haar uniqueness gives a positive nonnegative
real scalar comparing those inverse measures. Inverting back compares the
original lifts. Surjectivity of real averaging compares all compact quotient
test integrals, and regular measure extensionality gives equality of the
quotient measures. The conclusion writes the scalar as a strictly positive
real number `C` and the measure identity as `ν₁ = ENNReal.ofReal C • ν₂`.

Neither sigma compactness nor second countability is required. No left
invariance of the ambient group measures or unimodularity of the ambient
group is assumed. The subgroup measure is both left and right invariant,
as required by the existing positive lifting API. This helper does not
construct an invariant quotient measure or assume one exists: it compares
two supplied measures that satisfy the stated invariance properties.
