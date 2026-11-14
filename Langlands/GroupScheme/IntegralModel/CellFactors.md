# Integral generic factors extracted from actual cell coordinates

This internal construction concerns any integral model `M` over a domain `A`
with fraction field `K`, two integral factor models `MU`, `MP`, and compatible
model homomorphisms `φ`, `ψ` extending generic maps `i`, `p` into `M`.
It requires no local-ring, smoothness, connectedness or residue-field hypothesis.

`cellFactorSections` projects an actual integral coordinate in the product
`MU.group.X ⊗ MP.group.X` to its two original integral sections.
`cellFactorSections_product` identifies their product in `M` with the integral
cell multiplication of that coordinate.

Suppose the generic cell multiplication from the two factor groups is a
monomorphism. If the integral coordinate multiplies to a section `x` of `M`
and supplied generic factor points `u`, `v` multiply to the generic image
of `x`, `cellFactorSections_generic_eq` identifies `u` and `v` with the
generic images of the two extracted integral sections. The proof applies
naturality of integral-point maps and their multiplicativity to identify
the two generic products, cancels the generic cell monomorphism on the two
Cartesian lifts, and projects to the individual factors.

`integral_factors_of_cell_lift` records the consequence that the supplied
generic factors belong to their respective integral-point subgroups.
This conclusion retains the specified generic-fibre isomorphisms and the
compatibility squares of the actual model maps.

The provenance is internal category-theoretic composition and cancellation,
using the published integral-point naturality theorem and binary cell
multiplication. This is a factor-extraction step for opposite-cell arguments;
it assumes that integral coordinates have already been constructed and does
not assert that every integral product belongs to that cell.
