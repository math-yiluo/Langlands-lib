# The kernel of a flat affinization is anti-affine

This internal lemma supports the construction in SGA 3, Exposé VI_B,
Theorem 12.2. It applies to the unchanged `IsAffinization` predicate and the
actual scheme-theoretic kernel. The source group is quasi-compact over an
arbitrary field, and the supplied affinization homomorphism is flat.

The implemented proof uses flat base change of global sections. The global
sections of the kernel pair form the pushout of two copies of the source's
functions over the affine target's functions. Since the affinization induces
an isomorphism, either projection of the kernel pair induces an isomorphism
on functions. The published kernel-pair isomorphism identifies its first
projection with the projection from the product of the source and the full
kernel. Applying the same global sections pushout theorem over the field,
then faithfully flat descent along the nonzero algebra of source functions,
shows that the structure map of the full kernel induces an isomorphism.

Separatedness of field group schemes and quasi-compactness of the source
supply the required qcqs conditions, including those of the closed kernel.
This lemma supplies neither existence nor flatness of an affinization.

Source identifier: `sga3-expose-vib-gille-polo-2024`, Theorem 12.2(iv),
printed page 430 / PDF page 100, Gille–Polo recomposed edition of 13 October
2024. Source SHA-256:
`88d8ccb045fc959535155eb4b0fc72e3e4845730fb73355f2043e8023b7db3d2`.
The complete Tome I errata of that date do not modify the cited result.
