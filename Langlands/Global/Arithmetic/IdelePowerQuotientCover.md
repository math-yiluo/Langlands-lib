# Arithmetic data for an S-unit cover of idele power classes

Authors: Worker 450 and Worker 107.

For any number field `K : Type u`, this module chooses a finite set `S` of
finite places such that the principal ideles and the existing subgroup
`IdeleSUnits.sUnitIdeles K S` generate the actual idele group. It also proves
that the principal ideles inside `sUnitIdeles K T` form a finitely generated
subgroup for every finite set `T`. All declarations are in
`Langlands.Global.Arithmetic.IdelePowerQuotientCover`.

The definition `places K` chooses the finite set supplied by
`IdeleSUnits.exists_hasGlobalUniformizers K ∅`. The theorem
`hasGlobalUniformizers_places K` records the resulting property: every finite
place outside the chosen set has a global element with uniformizer exponent
there and unit exponents at the other places outside the set. The theorem
`principal_sup K` applies the existing
`IdeleSUnits.principal_sup_sUnitIdeles` to obtain
`principalIdeles K ⊔ sUnitIdeles K (places K) = ⊤`.

The theorem `principal_intersection_fg K T` identifies
`(principalIdeles K).subgroupOf (sUnitIdeles K T)` with the range of
`IdeleSUnits.sUnitsToIdeles K T`. The group of `T`-units is finitely generated
by the existing instance in `SUnitIndex`. The proof converts its monoid
finite-generation instance into group finite generation, passes to the range
of the homomorphism, and converts that instance into the subgroup predicate
`Subgroup.FG`.

This is an internal arithmetic adapter for the positive-power quotient
argument. Its inputs are the proved class-group construction in
`IdeleSUnits` and the proved finite generation of S-units in `SUnitIndex`;
it adds a choice of the finite set and the image argument above. The subgroup
`principalIdeles K` is the existing principal subgroup used to define
`IdeleClasses K`. No topology or profiniteness conclusion is asserted here.
