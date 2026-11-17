# Detecting root signs by actual contracting subgroup ranges

This derived unit works with an affine group over an arbitrary commutative
base ring, a supplied coordinate split torus and actual torus-equivariant
root maps. Its sign-detection conclusions additionally require a nontrivial
base ring and genuine `IsRootParametrization` certificates.

`rootPoint_mem_centralizer_of_zero` expands the actual conjugation orbit on
every scheme test. Torus equivariance and zero exponent make this orbit
constant. The all-test range version factors the actual root map into the
affine centralizer representative through `rootToAffineCentralizer`; its
companion equation recovers the original ambient map.
`rootPoint_mem_parabolic_of_nonneg` combines positive-root contraction with
this zero-root centralization, so zero roots are retained.
`cocharacter_neg_eq_opposite` proves the exact opposite-cocharacter equation
for the original coordinate exponent maps.

`rootPoint_one_ne_one` uses the root parametrization's monomorphism. Equality
of its scalar-one and scalar-zero points would imply equality of those points
in the additive line. Its actual coordinate and the global-sections/spectrum
isomorphism would then imply one equals zero in the base ring.

`coPairing_pos_iff_range_root_le_unipotent` characterizes strictly positive
root pairing by containment of the actual all-test root range in the
contracting functor. The positive direction uses the existing root contraction.
If pairing is nonpositive, the scalar-one point belongs to the opposite
parabolic. Membership in the original contracting functor would put it in
the trivial opposite-unipotent/parabolic intersection, contradicting its
nonidentity. `coPairing_pos_iff_of_unipotent_eq` applies this characterization
to two equal actual contracting functors.

Provenance is actual torus equivariance, fixed coordinate exponent
cocharacters, represented centralizer factorization, additive-line coordinates
and the published all-test opposite-intersection theorem. This unit does not
assume a desired filtration equality, and does not compare maximal tori or
perform global descent.
