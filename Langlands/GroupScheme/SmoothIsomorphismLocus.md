# Isomorphism neighbourhoods for smooth affine connected groups

`OpenIsomorphismStatement` records the all-base comparison and
`openIsomorphism` proves it. `exists_open_affine` gives the affine construction;
`exists_open` uses an affine chart through the specified field-valued point.

This internal comparison uses locally constant ranks of the actual relative Lie
modules. For a monic map between smooth affine group schemes whose source and
target have geometrically connected fibres, an isomorphism at a field-valued
point extends to an isomorphism over an open neighbourhood through which that
point factors. The affine-base proof fixes both Lie ranks near the point, uses
the smooth connected field-group comparison on every resulting residue fibre,
and applies the fibrewise open immersion criterion plus surjectivity.

The auxiliary fibrewise isomorphism criterion is the published argument of
`RelativeRoot.isIso_of_residueField_fibres` in `LocalRootProducts`, generalized
out of its private namespace. It uses flatness and finite presentation of the
source and local finite type of the target. All content is internally derived
from published Library and Mathlib results. Geometric connectedness of both
families is required in the comparison.
