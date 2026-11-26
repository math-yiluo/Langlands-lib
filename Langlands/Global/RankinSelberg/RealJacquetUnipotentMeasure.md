# Unipotent measure for real open-cell integrals

`entryHaar μ m` transports the product of a supplied real additive Haar measure `μ` on the
strictly upper entries to the upper unipotent subgroup of `GL_m(ℝ)` (with its Borel
structure). `entryHaar_isHaar` records that it is a Haar measure (from the Library's
`upperEntryProductMeasure_isHaar`), and `entryHaar_sigmaFinite` transports sigma-finiteness
along the measurable entry equivalence.

`unipotentProductMeasure_entryHaar` checks the normalization for the ordered product
`(u, v) ↦ diag(u, 1) n(v)` of the Library's `unipotentProductMeasure`. The entry coordinates
of the larger group split as the entries of the upper-left block and the last column. In the
product the last column is `u v`; for fixed `u` this linear change of variables has
determinant one (`det_upperUnipotent`) and preserves the product Haar measure of the column.
Together these give equality of the two measures on the larger group.

`transposeReflection m` permutes the entry coordinates by `(i, j) ↦ (j^rev, i^rev)`.
`transposeReflection_eq` identifies it at positive rank with `u ↦ w uᵀ w`, `w` the long Weyl
matrix, and `measurePreserving_transposeReflection` proves that `entryHaar μ m` is invariant
under it.

The module is the real counterpart of `ComplexJacquetUnipotentMeasure`, with the same proofs
for the real field. These measure identities support the successive unipotent integrations
in Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §7.2, pp. 47–48.
