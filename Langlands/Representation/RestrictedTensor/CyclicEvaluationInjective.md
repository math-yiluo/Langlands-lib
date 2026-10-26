# Injectivity of cyclic tensor evaluation

This internal helper specializes the published cyclic evaluation to coordinate
restrictions of a representation of the actual cofinite restricted product.
The field, index, local group, and ambient vector universes remain independent.
No topology or irreducibility of the ambient representation is assumed.

`localAction` is restriction along the genuine singleton homomorphism.
Coordinate extensionality proves that different singleton insertions commute;
the representation law gives `localAction_commuting`. `finiteInsertion`
inserts a tuple on a finite set and identity elsewhere, using the published
finite splitting equivalence. Its singleton formula is proved coordinatewise.

`stageAction` is the published finite external tensor product of the cyclic
subrepresentations. The coordinate equivariance already proved for evaluation
extends to this whole finite product: the group elements for which evaluation
commutes with the actions form a submonoid, and the coordinate singletons
generate the finite product. `stageIntertwiner` bundles this identity.
The all-generator pure tensor maps to the original vector, so a nonzero
original vector makes this intertwiner nonzero, including at the empty stage.

If every local cyclic representation is irreducible and its self-intertwiners
are scalars, finite external tensor irreducibility makes the nonzero stage
intertwiner injective. Finally, every element of the algebraic direct limit
has a finite-stage representative. Applying finite-stage injectivity to a
representative of a difference proves `eval_injective`.

The provenance is internal: the argument combines the published
`CyclicEvaluation`, restricted-group splitting, finite external tensor
irreducibility, and Mathlib's injective-or-zero theorem for intertwiners.
It does not assert full restricted-product equivariance, surjectivity,
selection of local factors, or the Flath existence theorem.
