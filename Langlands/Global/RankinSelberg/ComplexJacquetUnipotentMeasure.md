# Unipotent measure for the complex open-cell Jacquet integral

`entryHaar` transports the product of the supplied complex additive Haar
measure on strictly upper entries to the actual upper unipotent subgroup.
The published entry-coordinate theorem gives Haar invariance, and the
measurable equivalence transports sigma finiteness.

`unipotentProductMeasure_entryHaar` verifies the normalization for the
ordered product \((u,v)\mapsto\operatorname{diag}(u,1)n(v)\). The entry
coordinates split as the smaller upper-left entries and the last column.
In the product the occupied column is \(uv\). At each fixed \(u\) this
linear change has determinant one and preserves the supplied additive
product Haar measure. Together these steps give equality of the two
measures on the larger group.

`transposeReflection` permutes the entry coordinates by
\((i,j)\mapsto(j^{\mathrm{rev}},i^{\mathrm{rev}})\).
`transposeReflection_eq` identifies this map at positive rank with
\(u\mapsto w u^T w\), where \(w\) is the long Weyl matrix.
`measurePreserving_transposeReflection` proves exact invariance of
`entryHaar` under that permutation.

These measure identities support the successive unipotent integrations
in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §7.2,
pp. 47–48.
