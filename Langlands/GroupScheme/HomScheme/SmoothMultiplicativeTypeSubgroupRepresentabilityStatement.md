# Smooth moduli of closed subgroups of multiplicative type

Author: Worker 872.

`MultiplicativeTypeSubgroupModuli.SmoothMultiplicativeTypeSubgroupRepresentabilityStatement.{u}`
asks, for every smooth affine actual group scheme `G/S` over an arbitrary
scheme in universe `u`, for a smooth parameter scheme `M/S` and an actual
closed subgroup `j : K ⟶ G_M` of relative multiplicative type.
The family must satisfy the imported all-test universal property:
each actual closed multiplicative-type subgroup functor of `G_T`,
for each scheme `T/S`, is the evaluated range of `j` at a unique
parameter morphism `T ⟶ M`.

This includes nonsplit forms, finite nonsmooth diagonalizable factors,
and locally varying finitely generated abelian character groups.
It imposes no Noetherian or connectedness hypothesis on the base or
the ambient group. It does not require the parameter scheme to be
affine, quasi-compact, or separated.

The source is SGA 3, Exposé XI, Theorem 4.1, registered as
`sga3-exposes-xi-xii-xiv-gille-polo-2008`: `Expo11.pdf`,
PDF page 20, recomposed page 104, original page 157.
The source represents the multiplicative-type subgroup functor by
a smooth separated scheme; the present proposition omits
separatedness and uses the finite-character-type, actual
closed-subgroup interface of the imported module.
The universal actual subgroup is the subgroup corresponding to the
identity morphism of the representing scheme.

This module defines the proposition and proves no instance of it.
Its intended application is a conditional reduction to the unchanged
Library étale lifting target, using a pointed étale section of this
smooth parameter scheme. That reduction is a separate obligation.
