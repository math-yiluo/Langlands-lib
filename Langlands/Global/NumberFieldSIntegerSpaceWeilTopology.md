# Original number-field local coordinates of a space Weil restriction

This internal arithmetic specialization treats the finite-field,
completed-integer, and infinite-place coordinates of the Weil restriction
of an algebraic space over number-field S-integers.

Let `L/K` be an extension of number fields and `S` a finite set of finite
places of `K`. The lower coefficient ring is the original ring of
S-integers of `K`; the upper coefficient ring is the ring of S-integers of
`L` for the full preimage of `S`. Let `X` over the upper ring be
quasi-separated and of finite type. Assume explicitly that its Weil
restriction to the lower ring is algebraic.

`fieldPointHomeomorph` identifies the original Weil space's points at
`K_v` with the product of the original `X(L_w)` over places `w` above `v`.
The source and targets have their original field-valued point topologies.
The proof applies the finite-type tensor field comparison to
`NumberFieldSIntegerFieldTensor.tensorEquiv`. The actual completion maps
give continuous scalar multiplication. Completeness of the lower field
and finite dimensionality give the module topology. The published local
field results give henselianity for each independently normalized
completion norm. No preservation of those norms under ramified embeddings
is required.

For `v` outside `S`, `integralPointHomeomorph` identifies the Weil space's
points at the completed integers of `K_v` with the product of
`X(O_w)`. Each topology is induced by the original inclusion into the
corresponding field-valued points. The proof applies the integral tensor
topology comparison to the original completed-integer and completed-field
tensor equivalences. Compatibility of the coefficient inclusions is
definitional for the published original coefficient structures.

`infinitePointHomeomorph` treats every infinite place, including all real
and complex factors, using `NumberFieldSIntegerInfiniteTensor.tensorEquiv`.
Completeness and finite dimensionality supply the module topology and the
published infinite-completion result supplies henselianity.

Each homeomorphism has a component theorem identifying its forward map
exactly with `completedTensorSpaceWeilRestrictionPointMap` for the
specified original tensor equivalence. The additional
`isHomeomorph_fieldPointMap` supplies that property for the field map in
the form used by the integral construction.

The provenance is internal application of the published arithmetic tensor
equivalences and complete-local-field results to the tensor comparison
constructions. No choice of a projective chart or scheme model is imposed
on `X`. Algebraicity of its original Weil restriction is retained as a
premise. This unit does not assemble the adelic stages or prove the adelic
endpoint.
