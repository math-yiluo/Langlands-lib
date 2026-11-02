# Weil compatibility of the discrete fundamental-domain measure

This internal bridge identifies the explicit discrete left-quotient measure
with the existing `Langlands.QuotientIntegration.IsCompatible` API. The ambient
group is locally compact and Polish, with its Borel measurable structure;
`Γ` is a discrete subgroup. The two APIs use definitionally the same left
quotient, and their positive right translations agree on representatives.

Counting measure on `Γ` is finite on compact sets: its discrete topology makes
every compact subset finite. The subgroup is closed, and second countability
of the ambient group makes it countable. Fiber integrability of continuous
compactly supported functions therefore permits `integral_countable` to identify
real orbital integration with the existing orbit sum. Each singleton has
counting mass one. Continuity of the actual real average supplies the strong
measurability required by the existing fundamental-domain unfolding theorem,
which proves the real Weil formula for `discreteQuotientMeasure`.

`discreteQuotientMeasure_isCompatible` assumes a nonzero locally finite ambient
measure invariant under both left and right multiplication. Its quotient
measure is exactly the pushforward of that measure restricted to the previously
constructed Borel fundamental domain. Nonvanishing, regularity and positive
right invariance come from `LeftCosetHaarMeasure` and its dependencies. The
published real averaging operator and complexification results give
integrability of the complex average and the complex Weil formula for every
continuous compactly supported complex function. In particular these are
integrable expressions, beyond an equality of totalized integrals.

`discreteQuotientBorelSpace` derives the Borel property of the inherited quotient
measurable structure from closedness and the Polish ambient group. The two
compatibility conclusions install this proved property in their types; they
do not require a separate Borel quotient hypothesis. `haarQuotientMeasure_isCompatible`
applies the result to the actual `Measure.haar`, retaining the explicit
hypothesis that it is right invariant. The subgroup normalization is counting
measure, so each subgroup point has mass one.

`compatibleHaarQuotientMeasure` bundles this exact Haar quotient measure with
its proved compatibility property; its underlying measure is definitionally
`haarQuotientMeasure`, as recorded by `compatibleHaarQuotientMeasure_val`.
It makes no additional choice of measure or rescaling.

Provenance is internal: the bridge combines pinned Mathlib counting-measure
integration and finite discrete compact sets with the existing Library
averaging, complexification, fundamental-domain and regularity constructions.
It proves no new identification with an external normalization convention.
Actual rational discreteness, reductive unimodularity, finite covolume,
probability normalization, split-centre comparison and reduction theory
remain separate obligations.
