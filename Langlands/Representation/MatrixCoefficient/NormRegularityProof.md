# Continuity and measurability of descended coefficient norms

`Langlands.coefficientNormRegularity` proves exactly
`Langlands.CoefficientNormRegularityStatement`, retaining the independent
group and carrier universes. It exposes two reusable component lemmas in
the `Langlands.UnitaryCentralCharacter` namespace.

`continuous_coefficientNorm` applies the quotient-map characterization of
continuity to the actual map `G → G / Z(G)`. By construction, the pullback
of the descended coefficient norm is the complex norm of the original
matrix coefficient. The published theorem
`matrixCoefficient_isLocallyConstant` makes this coefficient locally
constant when its vector is smooth. Its continuity, followed by continuity
of the norm, supplies the required continuous pullback.

`aestronglyMeasurable_coefficientNorm` uses that continuity and Mathlib's
almost everywhere strong measurability theorem for continuous functions
with second-countable codomain. Here the codomain is the real line and
the domain has a Borel measurable structure. The measure is arbitrary;
the proof uses no Haar property, finite-measure assumption, or
sigma-finiteness. The closing theorem pairs continuity with this result
for each Borel measurable structure and each measure.

## Internal provenance and scope

This is an elementary deduction from the published matrix-coefficient
local-constancy theorem and Mathlib's quotient-topology and measurability
APIs. The proof does not introduce a topology on the representation carrier.
It uses an arbitrary algebraic functional and assumes smoothness only of
the vector. The supplied unitary central character is the datum already
used to construct the same descended function in `ModuloCenter`.

This proof establishes the regularity needed to apply subsequent Lp
estimates. It gives no integrability bound, volume estimate, asymptotic
formula, or temperedness criterion.
