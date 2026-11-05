# Cocharacters, reflection commutators and closed subgroups

Author: Worker 1484.

This internal module derives all-test subgroup-containment facts from the
published cocharacter lattices and actual normalizer actions. It introduces
no structural assumption about semisimple groups.

`cocharactersLandingIn i F` is the submodule of integral cocharacters whose
composite with `i` has its full range in `F`. The subgroup laws on every test
scheme prove closure under addition and integer multiplication.

The coordinate characters and cocharacters of a split torus decompose its
identity homomorphism as a finite sum. Evaluating this identity and applying
the pointwise subgroup laws proves `IsSplitTorus.range_le_of_cocharacters`:
if every cocharacter lands in `F`, then the whole torus lands in `F`.

`cocharacter_torusCommutatorEnd_mem` uses the published formula for the
actual commutator endomorphism of a normalized torus. Its values are
commutators on all test schemes.

For a closed subgroup, `mem_cocharactersLandingIn_of_zsmul_mem` proves
saturation: a nonzero integer multiple of a cocharacter landing in the
subgroup forces the original cocharacter to land in it. Multiplication by
that integer on the multiplicative group scheme is flat and surjective,
and it is quasi-compact because the source and target are affine.
Effective-epimorphism descent for membership in a monomorphism then removes
the integer multiple. No surjectivity on points of an arbitrary test scheme
is assumed.

For an actual root datum `P` of `i`, the perfect lattice pairing and its
compatibility with automorphisms show that an automorphism acting by the
reflection at a root negates the associated coroot. Composing that coroot
with the torus commutator endomorphism therefore gives minus twice the
coroot. Saturation removes this nonzero integer. Thus
`IsRootDatumOf.coroot_mem_cocharactersLandingIn` puts each coroot in every
closed subgroup containing all commutators.

These proofs work over every field, in arbitrary universe `u` and in every
characteristic, including characteristic two. The integer minus two is an
integer acting on a torus; its multiplication map remains faithfully flat
in characteristic two. All containment conclusions concern every test
scheme, including nonreduced tests. The module proves neither existence of
root data nor a generation theorem for a reductive group.
