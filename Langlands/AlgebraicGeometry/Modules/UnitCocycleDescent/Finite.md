# Common local frames for finite families of unit cocycles

Author: Worker 1232.

This internal construction extends the published local unit-cocycle section
theorem to a finite family on one common open neighbourhood. For an affine,
flat, surjective morphism `p : X → Y`, each coordinate is a natural,
multiplicative family of global units on all pairs with equal composite to
`Y`. `FiniteLocalFrame p c y` contains an open neighbourhood of `y` and one
invertible cocycle section for every coordinate on its preimage.

The proof applies
`UnitCocycleDescent.exists_unit_cocycleSection` with the proved algebraic
input `Langlands.Algebra.unitCocycleLocalUnits`. It intersects the finitely
many resulting neighbourhoods and restricts the unit sections to that
intersection. Restriction preserves both invertibility and the cocycle
section law. `finiteLocalFrame` chooses this data.

The construction is derived from the existing descent and restriction
APIs. It is intended for the finitely many unit coordinates of a split
torus. It does not yet convert a group-valued cocycle to these coordinates
or descend a corrected point to a section of a group quotient.
