# The global fixed locus of a special point's norm-one stabilizer

This internal construction proves global fixed-point uniqueness for the existing
norm-one stabilizer of any supplied special point of the actual
`ValuationBuildingData` quotient, at every field universe. Its hypotheses are
the existing apartment axioms, actual opposite-factor-pair existence,
injectivity of the existing apartment map, and common-apartment coverage for
points in the base apartment. None of these hypotheses is established here.

At a special point of the base apartment, the published
`SpecialPointFixedLocus.eq_of_compactStabilizer_fixed_of_isSpecialPoint`
already gives uniqueness among fixed points in that apartment's image.
The published `ApartmentFixedPointReduction` moves any fixed point into the
base apartment using a common apartment and the actual sharp fixer.
Combining these gives
`eq_of_compactStabilizer_fixed_of_special_apartmentPoint` on the entire
original quotient. This base-point theorem only needs common apartments with
that particular point.

The theorem `conj_mem_compactStabilizer` transports stabilizer membership
under every actual rational point `g`. The actual common rational-character
norm kernel is normal, so `g h g⁻¹` is norm one when `h` is.
The existing action laws show that it fixes `g • x` when `h` fixes `x`.
For a point `y` fixed by the stabilizer at `g • x`, these conjugate elements
therefore show that `g⁻¹ • y` is fixed by the stabilizer at `x`.
The base-point result gives `g⁻¹ • y = x`, hence `y = g • x`.
This is the implemented proof of
`eq_of_compactStabilizer_fixed_of_special_translate`.

The existing building special-point predicate supplies precisely a rational
translate of an apartment special point. Unpacking it yields
`eq_of_compactStabilizer_fixed_of_special_buildingPoint`.
Its common-apartment premise quantifies over every base-apartment point,
so it applies to whichever representative this predicate supplies.

`specialPointFixedLocusUnique` constructs a `Unique` structure on Mathlib's
actual fixed-point subtype for the subgroup `B.compactStabilizer z` acting on
`B.ReducedBuilding`. Its default element is the original supplied point `z`,
which every member of that subgroup fixes by its defining condition.
The global theorem proves that every other member of this subtype equals it.
Thus both existence of a fixed point and uniqueness hold, with the original
quotient, point, action and subgroup unchanged.

The provenance is internal composition of the two published fixed-locus
modules, normality of `Plancherel.rationalCommonNormKernel`, the existing
special-point definition, and group-action identities. No external source
assertion or extra rational-point surjectivity is used.

This unit does not construct the supplied building, apartment axioms,
opposite pairs, apartment injection, common apartments or a special point.
In particular it does not identify any integral-model image with a stabilizer.
The same-quotient supplied-model comparison and the unconditional
`IntegralModel.BuildingComparisonStatement` remain open.
