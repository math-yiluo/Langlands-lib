# Invariant subspaces and actual-root commutation

This internal supporting unit defines the actual roots whose rational images
belong to a subspace of the rational relative-root span. It excludes strict
positive mixed root combinations across a reflection-invariant subspace and
reuses `RootPairNoncommutation.commute_of_no_strict_combinations` from
[RootPairNoncommutation](../Reductive/RootPairNoncommutation.md), which already
applies to an arbitrary split acting torus. The final result proves irreducibility for any root system
whose root image is the full actual relative-root image of a maximal split
torus of an almost-simple group, provided that image is nonempty.

For an inside root and an outside root, the outside coroot annihilates the
invariant subspace. Symmetry of zero root-coroot pairing gives the reverse
vanishing. A strict positive mixed root, if inside, has nonzero pairing with
the outside coroot; if outside, it has nonzero pairing with the inside coroot.
Both contradict the same annihilation rule. Applying the semigroup commutator
theorem to these absent weights proves all-test root-group commutation.
This mixed-root exclusion works for any rational root pairing. Its commutation
application assumes a smooth affine ambient group and a split acting torus.
It needs no pinning, crystallographic hypothesis or reducedness condition.

For the final invariant-subspace and irreducibility results, the pairing is
assumed to be a root system on `relativeRootSpan i` with exactly the full
actual-root image under its subtype inclusion. Its coroot space may be any
rational module with the perfect pairing already required by `RootPairing`;
evaluation on the rational dual is not an extra premise.
The published empty-or-full commuting-partition theorem makes the roots lying
in an invariant subspace either empty or all roots. In a root system, a nonzero
invariant subspace contains a root, so the empty case is excluded. Containment
of all roots makes the subspace full. A nonempty actual root set makes root
space nontrivial, and Mathlib's field-valued irreducibility constructor supplies
the corresponding coroot-space condition.

The construction is internal content derived from Library root-pairing,
semigroup commutator and almost-simple root-partition results. It works over
any field and imposes no field or residue characteristic restriction.
The published `RelativeRootSystemIrreducibleStatement` accepts an arbitrary
full-image root pairing without an `IsRootSystem` premise; establishing that
premise from the actual root span is a separate remaining step. The local
affine-diagram target is also not proved here.
