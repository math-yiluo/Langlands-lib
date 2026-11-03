# Actual affine homogeneous quotients from cocycle orbits

Author: Worker 1471.

This internal construction turns a supplied actual affine orbit of the trivial
cocycle into the published `HomogeneousQuotient` record. It works over any base
scheme in an arbitrary universe. Let `a` act on a smooth affine group scheme
`G`, let `M : a.CocycleModel`, and let `j : C ⟶ G` represent the actual all-test
fixed subgroup. The additional input is an affine scheme `O` over the base,
a morphism `p : G.X ⟶ O`, a monomorphism `e : O ⟶ M.scheme`, and the equation
`p ≫ e = M.orbit`. The morphism `p` must be smooth and surjective.

`affineHomogeneousQuotientOfOrbit` uses exactly `O` and `p` as the quotient
scheme and projection. It derives local finite presentation of `O` by descent
along the smooth surjective `p`, since `G` is smooth over the base. Affineness
of `O` gives separatedness and quasi-compactness. Quasi-compactness of `p`
follows from quasi-compactness of its composite with the structural morphism,
which is the affine structural morphism of `G`.

For every scheme test and every pair of `G`-points, the monomorphism `e`
identifies equality after `p` with equality after `M.orbit`. The existing
`CocycleModel.orbit_fibers` theorem identifies this with membership of the
inverse-product in the fixed subgroup. The supplied representation identifies
that subgroup with the actual pointwise range of `j`. Thus all right-coset
fibers, including nonaffine and nonreduced tests, have the required meaning.
`affineHomogeneousQuotientOfOrbit_isAffineHom` records affineness of the
constructed actual quotient.

The provenance is internal: the construction combines the published cocycle
model, its full fiber theorem, the existing homogeneous quotient record and
local finite presentation descent. It does not construct a cocycle model or
an affine orbit, prove orbit smoothness, or prove reductivity. Those geometric
inputs remain explicit obligations for applications.
