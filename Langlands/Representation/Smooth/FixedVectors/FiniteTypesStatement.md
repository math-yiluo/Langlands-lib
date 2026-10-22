# Compact-open detection of a finite family of types

Worker 196 authored this internal statement from the finite-family interface
agreed with Worker 166 for the cuspidal constituent argument.

`Langlands.FiniteTypeCompactOpenDetectionStatement` quantifies an arbitrary
commutative coefficient ring R, group G, representation carrier V, second
carrier W, and finite index type with five independent universes. The group is
nonarchimedean and weakly locally compact. The representation rho is smooth.
There is no finite-dimensionality, admissibility or finite-length hypothesis.

For an open subgroup H, a finite family T of actual nonzero subrepresentations
of rho restricted to H, and an arbitrary identity neighborhood U in G, the
conclusion supplies one compact open subgroup K of G contained in U and H.
Every T_i has a nonzero vector fixed by the actual subgroup
`K.toSubgroup.comap H.toSubgroup.subtype` of H.

The same K is chosen before quantifying the second representation sigma. For
any such representation, if each atom of its H-subrepresentation lattice is
actually equivalent to some T_i as an H-representation, then each atom contains
a nonzero vector fixed by K in the ambient G-representation sigma. Equivalence
means Mathlib's `Representation.Equiv`, not equality of labels or a numerical
invariant. The second representation has no smoothness or semisimplicity
hypothesis. Atoms express simplicity of actual invariant subspaces. The type
family is allowed to be empty; the assertion then applies only to second
representations with no atoms. The result does not assert that an arbitrary
representation has such a finite type family.

This is an internal derived prerequisite. Its construction follows from the
published definitions of smoothness and fixed vectors, the compact-open subgroup
basis, and equivariant linear equivalences: choose one nonzero vector in each
family member, intersect finitely many open stabilizers with U and H, shrink to
a compact open subgroup, and transport the vectors through the specified
equivalences. The group restriction is tracked explicitly through subgroup
comap. The intended application is the fixed-vector choice in the proof of
Bernstein–Zelevinsky (1976), Proposition 3.30, step (3), printed page 37. This
statement isolates the elementary choice and transport; it does not claim the
block-isolation or constituent theorems in that source.
