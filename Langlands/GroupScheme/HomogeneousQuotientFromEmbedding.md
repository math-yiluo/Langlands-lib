# Smooth subgroup quotients from an exact-fiber ambient map

Author: Worker 148.

This internal derived module specializes the actual smooth relation quotient
construction to the published right-coset arrow scheme. It introduces no new
external geometric theorem. The ambient map remains an explicit hypothesis.

The arrow algebraic space is the space represented by the actual scheme
`G × H` over the base. Its source and target are the Yoneda images of the
published source `g` and target `g * i(h)`. `relation_iff` identifies sections of
this relation with membership of `g⁻¹ * h` in `SubgroupFunctor.range i` on every
scheme test. Arrow uniqueness for a monomorphic subgroup and the subgroup laws
prove `isEquivalenceRelation`. The identity atlas together with the actual
smooth source and target proves `hasSmoothProjections` when `H` is smooth.

`exists_quotient_of_map_kernel` starts with an actual smooth affine group over
any field at arbitrary universe, a smooth closed subgroup, and an actual map
into a separated scheme whose full scheme-test fibers are the right cosets.
It applies `schemeQuotientOfMapKernel` to obtain the actual scheme quotient,
smooth surjective projection, and monomorphism into the ambient scheme.
Separatedness follows by composing that monomorphism with the separated
ambient structural map. Local finite presentation descends along the smooth
surjective projection, and implies local finite type. The affine source is
quasi-compact, so its surjective continuous image is quasi-compact; this gives
quasi-compactness of the quotient over the affine base. Quasi-compactness of the
projection follows from quasi-compactness of its composite with the separated
quotient structural map. The final fiber criterion holds on every test scheme.

The conclusion is precisely the geometric and fiber data required by the
published smooth-subgroup quotient target. A separate construction of the
ambient exact-fiber map is still needed for the unconditional target.

`HomogeneousQuotient` packages this actual scheme, projection, geometric
properties and fiber criterion. `quotientOfMapKernel` chooses such data from the
existence theorem by classical choice.
