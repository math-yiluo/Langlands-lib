# Ordinary cohomological corestriction on the standard resolution

Author: Worker 45.

This pair constructs ordinary corestriction independently of the Tate
operation. A homogeneous subgroup cochain is precomposed with the
augmentation-preserving standard-resolution comparison and then sent
through the genuine relative trace on equivariant homomorphisms.

The component map is linear. Its cochain-map certificate follows from
commutation of the standard-resolution comparison with the boundary and
the proved compatibility of relative trace with ambient precomposition.
The existing bar/standard and inhomogeneous-cochain isomorphisms transport
it to `ordinaryCorestrictionCochainMap` on Mathlib's exact ordinary cochain
complex. `ordinaryCohomologyCorestriction` is the induced actual homology
map of that cochain map.

No Tate operation, comparison identity, or corestriction law is supplied
as an input. The construction works in arbitrary common universe `u` with
finite coset space. This pair makes no claim about its relation to Tate
corestriction.

This is the standard resolution and relative-trace construction described
by Serre, *Local Fields*, Greenberg translation, GTM 67 (1979), Chapter VII
section 7, printed pages 118–119 (PDF pages 124–125). The explicit comparison
with the pinned Mathlib cochain complexes is internal.
Registered source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
