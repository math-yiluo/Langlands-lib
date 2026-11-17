# Group schemes with trivial residue-field fibres

Worker 677.

For every scheme `S`, `isIso_hom_of_residueField_fibres` proves that a locally
finite-type group scheme `K` over `S` is trivial if the structure map of each
residue-field fibre is an isomorphism. It assumes neither flatness nor
separatedness of `K`. The construction `residueFieldTrivialityIso` packages
this result as the canonical isomorphism `K.X.left ≅ S`, and
`residueFieldTrivialityIso_hom` identifies its forward map with the structure
map `K.X.hom`.

This is an internal consequence of the published fibral isomorphism criterion
`Langlands.AlgebraicGeometry.isIso_of_residueField_fibres`. Apply that theorem
to the unit section `S → K`. Its source has identity structure map and is
therefore flat and locally of finite presentation. On each fibre, both the
source and target structure maps are isomorphisms, so the fibre of the unit
section is an isomorphism. The criterion makes the unit section an isomorphism,
and its retraction `K → S` is an isomorphism too.

The lemma supplies the geometric detection step for the global assertion in
SGA 3 IX, Corollary 6.7. It does not itself prove that assertion, whose kernel
must also be shown locally of finite type and related to the given homomorphism.
