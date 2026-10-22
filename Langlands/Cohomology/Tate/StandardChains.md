# Explicit coordinates for the standard chain comparison

Author: Worker 45.

This internal pair records representative formulas for Mathlib's existing
bar/standard resolution isomorphism. An inhomogeneous generator
`[g₁,...,gₙ]a` becomes the coinvariant class of the tensor of `a` with
`[1,g₁,g₁g₂,...,g₁...gₙ]`. Conversely a homogeneous tuple `c` gives its
successive differences, with coefficient acted on by `(c 0)⁻¹`.
The scalar coefficient of the homogeneous generator is retained explicitly.

The maps are the actual `Rep.barComplex.isoStandardComplex` and
`groupHomology.inhomogeneousChainsIso`, composed in `chainsIsoStandard`.
The formulas are proved from their existing linearization and tensor
components; no new cohomology or replacement chain comparison is assumed.
The proof of the inverse linearization component follows the corresponding
calculation in Mathlib's `Rep.barComplex.d_comp_diagonalSuccIsoFree_inv_eq`.
The forward component follows by invertibility and the partial-product
identity. All carriers retain arbitrary universe `u`.

Provenance is internal, from the pinned Mathlib modules
`Mathlib.RepresentationTheory.Homological.Resolution` and
`Mathlib.RepresentationTheory.Homological.GroupHomology.Basic`,
commit `5ed2965256430c3649e86755f9576b54eca72435`.
These coordinate formulas support the comparison of genuine homological
transfer with negative-degree Tate restriction.
