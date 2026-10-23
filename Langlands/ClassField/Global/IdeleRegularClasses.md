# The subgroup of regular idele-class cohomology classes

For a finite Galois extension `E/F` of number fields in an arbitrary common
universe, `IsRegularIdeleClass F E c` means that there exists a number-field
extension `L` of `E`, Galois over `F` and in the same universe, such that the
actual idele-class inflation of `c` lies in the image of the actual idele
quotient cohomology map over `L`. The definition uses the previously constructed
`ideleClassRegularSubgroup F E L` for each specified extension.

The common-extension theorem constructs a single finite Galois extension in
which two regular classes both have idele representatives. It applies
`commonGaloisOverfield` to their chosen witness extensions and then applies
`ideleClassRegularSubgroup_le` to each branch of the resulting compatible towers.
The embeddings agree on `E`; this is necessary to compare the original classes.

The definition `regularIdeleClassSubgroup` uses this common extension to prove
closure under addition. Zero is represented in `E` itself, and negation uses the
same witness extension. The final lemmas include every specified-extension
regular subgroup, and the image of the original idele quotient cohomology map,
in the subgroup of regular classes.

This is an internal derivation from `CommonGaloisOverfield` and
`IdeleRegularExtension`. The latter's inflation transitivity and representability
under enlargement supply the cohomological input. No reciprocity, local
invariant, or order-bound hypothesis is required. This file does not show that
every class is regular and does not assign invariants or prove the global
invariant statement.
