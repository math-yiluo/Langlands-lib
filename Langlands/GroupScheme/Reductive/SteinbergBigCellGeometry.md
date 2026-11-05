# All-test geometric steps for Steinberg big-cell data

This is an internal derived collection of geometric lemmas supporting
`SteinbergBigCellStatement`. It constructs no Borel subgroup, maximal torus,
regular cocharacter, Weyl representative, or highest-weight module.

For any affine group scheme over an affine base, reversing a cocharacter
leaves its full centralizer unchanged. A point in both opposite dynamic
parabolics has a limit in the centralizer. Dividing by that limit gives a
point of the first unipotent subgroup that also lies in the opposite
parabolic. The published all-test opposite-intersection theorem makes this
ratio the identity. This proves
`Dynamic.parabolic_inf_opposite_eq_centralizer` without smoothness or
reductivity hypotheses. For supplied representatives, equal images of two
parabolic points consequently factor through the supplied centralizer.
These conclusions retain all nonreduced and nonaffine test schemes.

If a coordinate evaluates to a global unit at a point of an arbitrary
relative test scheme, pullback of its principal open is the entire test
scheme. Thus its entire topological image is contained in the principal
open. An open immersion's universal property then lifts the whole test
scheme to a supplied open cell, giving global factors, rather than merely
local factors. The definition `SubgroupFunctor.cellPointLift` constructs
this actual morphism to the product representing the cell. Its
`cellPointLift_comp` identity proves that multiplication recovers the
original point. Projecting this lift gives the two global factors.

For a smooth affine field group, let supplied maps represent `P(chi)`,
`P(-chi)` and `U(chi)`. Assume explicitly that the principal open of a
supplied coordinate lies in the image of multiplication
`U(chi) x P(-chi) -> G`. The published opposite-cell theorem makes this
multiplication an open immersion. Its global factors, the containment
`U(chi) <= P(chi)`, and inversion of the second factor prove
`Dynamic.exists_opposite_parabolic_factors_of_unit`, the form needed in
condition 5 of Steinberg big-cell data.

The principal-open containment is a genuine remaining hypothesis. This file
does not identify a matrix coefficient's nonvanishing locus with the cell,
identify a centralizer with a diagonalizable maximal torus, conjugate the
two parabolics, or prove Steinberg irreducibility. The provenance is the
explicit argument above from published Library results and Mathlib's
scheme-theoretic open-immersion and principal-open operations.
