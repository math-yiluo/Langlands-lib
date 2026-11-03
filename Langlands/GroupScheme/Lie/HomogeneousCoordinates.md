# Natural homogeneous coordinates on actual Lie kernels

This is an internal change-of-basis construction from the existing actual
coefficient-extension maps and finite Lie coordinates. It introduces no new
geometric premise or literature assertion.

Let `G` be an affine group scheme over any field `k` in universe `u`, and let
`c : Lie.FiniteCoordinates G d`. For any finite basis `v` of the actual
base-field module `Additive (lieKernel G k)`,
`Lie.FiniteCoordinates.inBasis c v` gives natural finite Lie coordinates in
the extended basis `c.baseChangeBasis v A` over every commutative test
`k`-algebra `A`.

`baseChangeBasis_naturality` first proves that actual coefficient change
takes each extended basis vector to its counterpart. In the original
coordinates this follows from naturality along the base-field algebra maps
and the fact that an algebra homomorphism commutes with those maps.
`baseChangeBasis_equivFun_naturality` then expands a vector in the extended
basis and applies the semilinearity of actual coefficient change.

`basisTransition c v A` is the linear equivalence from the original
`Fin d` coordinates to these new coordinates. Its naturality theorem
commutes this equivalence with every coefficient-algebra morphism. The
indices of the original and chosen bases need not be definitionally equal.

For a supplied `HomogeneousLieBasis q` of an actual action `b` restricted
along `j`, `HomogeneousLieBasis.differential_coordinates` proves that the
original differential is diagonal in `c.inBasis q.basis`: coordinate `i`
is multiplied by the actual value of `q.weight i` at the given torus point.
The proof expands the vector in the extended basis, applies the already
proved eigenvector equation to every summand, and extracts coordinate `i`.

The construction retains arbitrary field characteristic, repeated and zero
characters, arbitrary universe `u`, and the empty basis. It constructs Lie
coordinates and their differential formula; all-test vector-group
diagonalization, semigroup-subgroup identification, and the ordered-product
theorem remain further obligations.
