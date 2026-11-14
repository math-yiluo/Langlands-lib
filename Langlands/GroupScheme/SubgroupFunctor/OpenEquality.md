# Equality of smooth subgroup images near a residue fibre

This internal construction turns containment of two smooth subgroup images into
an equality on a specified base open. Let `i : H ⟶ G` and `j : K ⟶ G` be
monomorphisms on underlying schemes over an arbitrary scheme `S`, with `H/S`
and `K/S` smooth and `K/S` geometrically connected. Assume containment of their
ranges on every test scheme.

`rangeFactor` is the unique factor `H ⟶ K` constructed by the represented-subgroup
factorization API. Its composite with `j` is `i`; hence it is monomorphic.
`rangeEqualityOpen` is the inverse image of its étale locus along the unit of `H`.
On this canonical open the factor is an isomorphism by
`SmoothMonoLocalIso.isIso_unitEtaleOpen`. The two subgroup ranges therefore
agree on every test scheme over this open.

If the subgroup ranges agree after pullback to the residue field of a base
point `s`, the two monic presentations of that fibre subgroup are isomorphic.
Uniqueness of factorization identifies the residue factor with that isomorphism.
Thus `s` belongs to `rangeEqualityOpen`, by
`SmoothMonoLocalIso.mem_unitEtaleOpen_of_residueFiber`.
`exists_open_range_eq_of_residue_range_eq` packages the open and its properties.

The construction is internal: it combines represented-subgroup factorization
and uniqueness, arbitrary base change, and the smooth monomorphism local
isomorphism construction. There is no affine or quasi-compactness assumption.
Containment remains a hypothesis; this module does not assert that equality of
one fibre alone implies local equality of two varying subgroups.
