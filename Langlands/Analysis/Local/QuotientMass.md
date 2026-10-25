# Positive finite mass in an actual left quotient

Authors: Worker 408 and Worker 113.

This internal helper uses the existing actual left quotient
`LeftQuotient H = Quotient (QuotientGroup.rightRel H)` and its existing
right-translation homeomorphisms. It proves positivity and finiteness for
the supplied compatible measure; it does not choose a quotient measure or
compute a numerical orbit-volume ratio.

`compactOpenQuotientOrbit H J` is exactly the image of the open subgroup
`J : OpenSubgroup G` under `leftQuotientMap H`. Its name does not assert
compactness of `J`. The separate lemmas show that this image is open, is
nonempty because it contains the identity coset, and is compact when `J`
is compact. They use the already published open quotient map and its
continuity.

`IsCompatible.isOpenPosMeasure` proves that every nonempty open subset of
the quotient has positive measure. Compatibility supplies a nonzero regular
measure and measure-preserving right translations. Regularity gives a
compact set `K` of nonzero mass. Given a nonempty open set `U`, choose a
representative `u` of one of its cosets. A coset represented by `x` lies
in the preimage of `U` under right translation by `x⁻¹ * u`. These open
preimages therefore cover `K`, so finitely many cover it. If `U` had zero
mass, invariance would give zero mass to each of those finitely many
preimages and hence to `K`, a contradiction. The proof uses neither the
averaging-integrability field nor the integral-formula field of
compatibility.

`IsCompatible.measure_pos_lt_top` combines this full-support result with
the fact that a regular measure is finite on compact sets. Its hypotheses
are exactly compactness, openness and nonemptiness of the set.
`IsCompatible.compactOpenQuotientOrbit_mass` specializes it to the image
of a compact open subgroup. No normality of `H`, normalization relation
between the subgroups, second countability, local compactness, or fixed
Haar normalization is added. The ambient and subgroup measurable structures,
measurable multiplication on the subgroup, right invariance of its measure,
and the compatibility predicate are retained as required by the imported API.
The quotient carries its Borel measurable structure.

The intended consumer is the equal-rank compact-test construction: its
quotient support is a nonempty compact open set, so these lemmas supply
the positive finite mass needed for scalar normalization for every
compatible measure. They do not construct coefficient vectors,
Schwartz–Bruhat tests or a unit-value integral, and do not prove
`EqualRankUnitValueStatement`.

The provenance is internal. The proof adapts the finite-cover argument
behind Mathlib's `isOpenPosMeasure_of_mulLeftInvariant_of_compact` to the
already published right-translation action on the actual left quotient.
It uses `Measure.Regular.exists_isCompact_not_null`, the finite open
subcover theorem and measure-preserving preimage identities directly.
Worker 113 supplied the regularity and finite-cover proof-route
observations during coordination; Worker 408 implemented the module.
