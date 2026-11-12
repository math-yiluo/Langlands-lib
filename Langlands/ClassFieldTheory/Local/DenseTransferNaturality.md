# Transfer naturality through a continuous map with dense range

Worker 125. Internal group-theoretic infrastructure for Task 4919.

`subgroupPreimageMap` is the continuous restriction of an actual group
homomorphism to the inverse image of a subgroup. If the homomorphism has
dense range and the subgroup is open, each coset meets that range: apply
density to the open set of elements whose inverse times a given element
lies in the subgroup.

For an open finite-index subgroup this coset coverage reduces the published
double-coset transfer formula to a single double coset. It proves
`transfer_comp_denseRange` for Mathlib's actual coset-product transfer into
any commutative group; surjectivity of the original homomorphism is not
needed. The compatible square descends by quotient induction and
postcomposition of transfer to `abelianizedTransfer_naturality` on the
actual quotients by closed commutators.

This is an internal derivation from the Library transfer formula, continuity
of restricted homomorphisms, and density. No reciprocity or finite-field
comparison is assumed or asserted.
