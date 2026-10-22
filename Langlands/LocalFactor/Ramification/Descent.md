# Maps and fixed spaces for a supplied finite inertia quotient

Worker 20 extends the published `Langlands.LocalFactor.Ramification.Galois`
construction without changing the finite ramification filtration or its sums.
The input is a surjective homomorphism from a group `J` to the actual finite
inertia group of a supplied finite p-adic field over its base field. A
representation of `J` comes with a proof that the kernel of this homomorphism
acts trivially. The published constructor then descends that representation.
No quotient is selected from an unproved existence assertion.

`descendInertiaMap` transports an intertwiner through this descent. Its
underlying linear map is unchanged: the equivariance proof lifts each element
of finite inertia to `J` and uses the original equivariance identity.
The construction preserves identity and composition. `descendInertiaEquiv`
uses the original linear equivalence, and `kernel_le_iff_of_equiv` proves
that the kernel condition is itself invariant under equivalence. Source and
target carriers have independent universes. These constructions require no
finite-dimensionality.

`fixedVectors_descend_eq` identifies the fixed subspace of any subgroup of
finite inertia with the fixed subspace of its actual inverse image in `J`.
This is an equality of submodules of the original carrier, not just an
equality of dimensions. Both implications follow by lifting group elements.
At the whole finite inertia group this is exactly the full invariant
subspace of the representation of `J`.

For finite-dimensional representations, the resulting codimension identity
gives

`Artin(quotient, rho) = dim(V) - dim(V^J) + Swan(quotient, rho)`.

The subtraction is the natural-number codimension, then embedded in the
rationals. Both terms on the left and right use the published actual
ramification-group sums. The Artin and Swan expressions at this same
supplied quotient are invariant under genuine representation equivalence.
Their independence from a different quotient, their integrality, and the
existence of a suitable arithmetic quotient remain separate theorem
obligations.

## Provenance and sources

The descent, map, and fixed-space arguments are internal consequences of
surjectivity and the definition of invariant vectors. The conductor identity
uses the already constructed zeroth ramification group and separates its
term from the Swan sum. It does not use character orthogonality or an
integrality theorem.

Jean-Pierre Serre, *Local Fields*, Greenberg translation, GTM 67 (1979),
Chapter VI, section 2, Proposition 2 and Corollary 1', printed pages 100–101
(retained PDF pages 107–108), gives the conductor sum with weights
`|G_i| / |G_0|` and the codimension of the fixed space. Printed page 99 and
pages 100–101 were read in the retained original. The additional quotient
independence result on page 101 is not claimed here.

Source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
retained at `C:/Central-Library/Serre--Local Fields--1979.pdf`.
Serre's classical conductor is for complex representations. As in the
published construction, the Lean rational weighted codimension expression
is defined for arbitrary coefficient fields; the intrinsic descent and
equivalence results do not identify it with an integral Artin character
outside the classical hypotheses.

The only project import is the published
`Langlands.LocalFactor.Ramification.Galois`, whose public constructors in
`Langlands.Ramification.Padic` are reused by name. Its actual integer-ring
action, residue-action inertia, and terminating lower groups are retained.
The fixed-vector submodule and restricted equivalence come from the
published representation layer. Mathlib's representation, linear-map and
linear-equivalence interfaces are used at pinned commit
`5ed2965256430c3649e86755f9576b54eca72435`.

This is a construction prerequisite for the Weil–Deligne conductor
correction. It is not an unconditional conductor constructor on the actual
local Weil group, and no nonabelian epsilon system is supplied.
