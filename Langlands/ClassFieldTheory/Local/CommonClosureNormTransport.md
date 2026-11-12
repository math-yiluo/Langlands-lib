# Norm transport between prescribed intermediate Weil groups

Worker 125. Internal derived infrastructure for Task 4919.

`intermediateInclusionEmbedding` is the literal inclusion of two finite
intermediate fields as an embedding over the specified p-adic base.
`intermediateWeilInclusion` transports the actual common-closure subgroup
inclusion to their standalone Weil groups through `intermediateWeilEquiv`.
Its projection identity follows from the two prescribed-field projection
formulas.

`reciprocityUnits_intermediateWeilInclusion` assumes geometric standalone
candidates and proves their norm square for this inclusion. The closure
comparison factors through the fixed closure of the original base field.
It extends the literal field inclusion, and its action commutes with the
Weil projections by the preceding identity. The closure-independent norm
lemma then applies. Neither field is assumed normal over the base.

`normalizedAbs_intermediateWeilEquiv_symm` proves the absolute-value
identity on the actual prescribed Weil subgroup for every supplied base
`TopologicalData`. Standalone geometric order gives the exponent over the
intermediate field; the residue-cardinality formula and scaling of the
integer degree convert it to the degree over the base. The published
independence of residue cardinality from the supplied topological datum
supplies exactly the requested base cardinality.

This is a derivation from the imported Library comparisons and geometric
norm theorem. It adds no external source or unconditional existence claim.
