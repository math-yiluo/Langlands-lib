# Regular idele-class cohomology under inflation and restriction

This internal unit proves functoriality of the subgroup of regular classes in
the actual idele-class `H²`, for number fields in an arbitrary common universe.

For a tower `F → E → K`, with `E/F` and `K/F` Galois,
`isRegularIdeleClass_inflation_iff` says that a class is regular exactly when its
inflation to `K` is regular. If the inflated class has a witness extension `L`,
inflation transitivity makes `L` a witness for the original class. Conversely,
the common-overfield construction combines an original witness with `K`;
representability under enlargement and inflation transitivity then give a
witness for the inflated class. This equivalence does not assert injectivity of
inflation. The definition `regularIdeleClassInflation` restricts the actual
inflation map to the regular subgroups.

For a tower `F → K → E` with `E/F` Galois,
`isRegularIdeleClass_restriction` proves that restriction to `Gal(E/K)` preserves
regularity. The intermediate extension `K/F` need not be normal. The proof uses
the original witness `L`, equips it with the composed `K`-algebra structure, and
restricts its idele representative. The quotient-map restriction square and
inflation/restriction commutativity identify the resulting class.
`regularIdeleClassRestriction` is the induced homomorphism of regular subgroups.
Both maps have explicit coercion evaluation lemmas.

The provenance is internal: the proof combines `IdeleRegularClasses`,
`IdeleRegularExtension`, `IdeleCohomologyTower`, and `CohomologyTowerProof`, without
new arithmetic hypotheses. It neither assigns invariants nor asserts that all
classes are regular; in particular, it is not a proof of the global invariant
statement or of a formula for invariant values under restriction.
