# Stable spatial cutoffs in induced point products

This internal module applies the actual right Kan extension coordinate formulas
to products of skyscrapers with independent coefficients. All category, group,
point-index, spatial and coefficient universes remain independent.

A spatial coordinate consists of a group element `g` and a point index `i`.
For a supplied map from point indices to a space with a group action,
`spatialCoefficientMask` keeps a coefficient exactly when
`g⁻¹ • π i` belongs to the selected set. This is the original spatial coordinate
of the section, before translation. A subgroup preserving the set makes the
family of coefficient transformations invariant under right multiplication.
The preceding stable-coordinate theorem therefore proves that `spatialCutoff`
preserves the existing locally discrete submodule. Its coordinate theorem
identifies the operation with the stated zero-or-identity mask.

The module also proves surjectivity of raw point-product restriction along
arrows injective on point fibers, by extending every coefficient function by
zero. Point fibers preserve monomorphisms, giving the monomorphism case.
Surjectivity passes to actual right Kan induction, by choosing a preimage
independently at every group coordinate and reindexing the family through the
bijection given by right multiplication by the inverse twist.

These results provide cutoff and extension operations. They make no assertion
of compact acyclicity or of smoothness for the unmodified raw extension.
