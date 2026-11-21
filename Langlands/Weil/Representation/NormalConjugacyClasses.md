# Conjugation on irreducible classes with open kernel

`Langlands.FiniteRepresentation.OpenKernelIrreducibleClasses H` is the
quotient of the finite-dimensional complex representations of `H` that
are irreducible and have open kernel, by actual linear intertwining
isomorphism. The carrier universe is independent of the group universe.
The test is openness in the supplied topology on `H`, with no additional
finiteness or compactness assumption. `openKernelIrreducibleRank` is the
complex dimension descended to this quotient.

If `N` is a normal subgroup of a topological group `G`, the module defines
the `G`-action on these classes for `H = N`. The element `g` acts by
pullback under conjugation by `g⁻¹`. This preserves irreducibility because
conjugation is surjective, and preserves the open kernel by continuity.
It preserves linear intertwining isomorphisms. The inverse convention
makes pullback a left action. The defining laws are implemented by the
identity map on the representation carrier. The supplied computation
lemmas show that the action does not change rank and that an element of
`N` acts trivially on these classes: its action operator is an invertible
intertwiner from the inner pullback to the original representation.

**Internal provenance.** This is the actual class interface needed to
apply the orbit-of-constituents argument to wild inertia as a normal
subgroup. The open-kernel condition selects the representations used on
the profinite subgroup. This module constructs the action; it does not
assert Clifford theory, extend representations, or count their orbits.
