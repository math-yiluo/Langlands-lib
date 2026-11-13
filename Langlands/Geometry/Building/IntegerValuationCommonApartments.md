# Common apartments for the actual integer-valued quotient

This supporting statement isolates a geometric obligation for the maximal
unramified building argument. It also proves two elementary transport lemmas
on the existing quotient and one-stabilizers. It does not prove that common
apartments exist.

For arbitrary apartment data `D : KPApartmentData i ω`,
`D.HasCommonApartments` means that for every two points `y, z` of
`D.ReducedBuilding`, there are actual rational points `g` and apartment
points `a, b` with
`g • D.apartmentMap a = y` and `g • D.apartmentMap b = z`.
The field, group, apartment, quotient relation and action are the existing
objects. The definition specializes the published predicate
`ApartmentQuotient.HasCommonTranslatedApartment` to `D.sharpFixerFamily`.
No auxiliary building or metric realization is substituted.

`exists_apartmentMap_eq_of_fixed_by_sharpFixer` assumes only that one such
apartment contains both `D.apartmentMap x` and `y`, and that the sharp fixer
of `x` fixes `y`. It proves that `y` is in the base apartment. Indeed, the
quotient equality between the representatives `(1, x)` and `(g, a)` gives
a normalizer element `n` such that `g * n` belongs to that sharp fixer.
The inverse of this element sends `g • D.apartmentMap b` to
`D.apartmentMap (n⁻¹ • b)`. Because the sharp fixer fixes `y`, this
apartment point still represents `y`. This argument needs no topology,
building axiom or reductivity beyond whatever is present in the data.

For `B : IntegerValuationBuildingData v G`,
`conj_mem_oneStabilizer` proves that conjugation by `g` sends an element
of `B.oneStabilizer y` into `B.oneStabilizer (g • y)`.
The character-valuation kernel is normal, and the stabilizer condition
transports by the original group action. The valuation is any supplied
integer-valued valuation.

`MaximalUnramified.CommonApartmentsStatement.{u}` specializes the common
apartment obligation to every nonarchimedean local field `F`, affine `G`
over the actual `inertiaFixedField F`, and supplied
`B : MaximalUnramified.BuildingData F G`, at arbitrary universe `u`.
The valuation is the prescribed `MaximalUnramified.valuation F`.
No local-field structure on the inertia fixed field is assumed.

The provenance is internal. The quotient transport proof adapts the
published local-field `ApartmentFixedPointReduction` to generic apartment
data by using the same quotient relation directly. The other lemma unpacks
normality and the one-stabilizer definition. This unit supplies neither
the common-apartment witness nor a singleton vertex fixed locus,
algebraic boundedness, bounded-subgroup fixed points, or maximality.
