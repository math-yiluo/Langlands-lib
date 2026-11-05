# Geometry of finite-type groups of multiplicative type

Author: Worker 1341.

These are internal consequences of the published `IsMultiplicativeType`
definition. They retain its arbitrary splitting extension and finitely
generated full character group, including torsion.

`MultiplicativeTypeGeometry G` packages affineness of the underlying scheme,
local finite type of its structure map, and commutativity of the group object.
`IsMultiplicativeType.geometry` proves this package, with separate projection
lemmas for its three properties and for affineness of the structure map.

Affineness follows by transporting the affine diagonalizable model along
the given actual group-scheme isomorphism and applying the published
field-extension affineness descent theorem. Finite type follows by
transporting the finite-type diagonalizable structure map and descending
that property along the faithfully flat, quasi-compact field extension.
Commutativity follows from the natural isomorphism on all test-point groups
and faithful flat descent of commutativity of the group object.

These results assert neither smoothness nor reducedness and impose no
characteristic or perfectness restriction.
