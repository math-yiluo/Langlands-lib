# A torus centralizer equality near a regular residue fibre

This module uses the smooth monomorphism helper `SmoothMonoLocalIso`
(module `Langlands.GroupScheme.SmoothMonoLocalIso`). This module is an internal
comparison construction and does not prove the opposite Borel target.

Let a torus inclusion and a cocharacter of that torus be supplied, together with
a representative of the ambient cocharacter centralizer. The comparison
homomorphism maps the torus to that representative. Its composite with the
centralizer inclusion is the original torus inclusion, because points of a
commutative subgroup centralize its cocharacters.

If the original torus inclusion is closed and the dynamic centralizer equals
its image on a residue fibre, the fibre comparison is an isomorphism. Indeed,
the torus and centralizer fibre represent the same subgroup functor, so their
compatible representative isomorphism equals the fibre comparison by monicity.

For a reductive ambient group and a split torus, the torus and represented
centralizer are smooth. The centralizer has geometrically connected fibres:
the ambient group does by its field-valued reductive fibres, and the published
dynamic smooth-connected theorem transfers this to the centralizer.
The comparison is monomorphic because its composite is the closed torus
inclusion. `SmoothMonoLocalIso.isIsoNear_of_residueFiber` therefore makes the
comparison an isomorphism on an open neighbourhood of the specified point.
Its image equality with the centralizer then gives the required all-test
centralizer equality on that open.

This is a derived support argument for constructing a regular local
cocharacter through the specified torus. It does not assert that such a
cocharacter or the residue-fibre centralizer equality has been supplied.
