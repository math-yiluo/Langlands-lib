# Additive Haar null sets and Haar measure on units

`Langlands.Analysis.measure_preimage_unitsVal_eq_zero` pulls measurable
additive Haar null sets back to Haar null sets on the unit group. The ring is
locally compact and second countable, with an open unit locus. Its unit group
is second countable and its Haar measure is sigma-finite. Both spaces have
their Borel measurable structures.

Write `ν` for additive Haar measure and `μ` for Haar measure on the units. For
a measurable `ν`-null set `Z` and each unit `g`, the set of `a` with
`a * g ∈ Z` is `ν`-null. Right multiplication by `g` is an additive
homeomorphism, and uniqueness of additive Haar measure gives the nullity of
this preimage. By Fubini, for `ν`-almost every `a` the set of `g` with
`a * g ∈ Z` is `μ`-null. The open unit locus has positive `ν`-measure, so
some such `a` is a unit. Left invariance of `μ` under this unit gives the
claim. The comparison supplies the measure step from the matrix algebra to
the general linear group in the regular-locus proof.
