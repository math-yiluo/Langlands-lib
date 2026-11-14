# Irreducibility of the relative root system

Worker 237, with Worker 227, whose shared exact-type proof draft is reused here.

`Langlands.GroupScheme.relativeRootSystemIrreducible` proves the published
`RelativeRootSystemIrreducibleStatement.{u}` at every universe `u`. It retains
all hypotheses: an arbitrary field, an almost-simple group, a maximal split
torus with nonempty relative roots, and any root pairing on the rational
relative-root span with the specified evaluation pairing and full root image.
There is no restriction on characteristic, including characteristic 2.

Almost-simplicity supplies the affine structure-map instance. The proof then
applies the published `isIrreducible_fullRelativeRootPairing` to the given
pairing and full-image equality. This support theorem first obtains finiteness
from the actual split-torus Lie weights and obtains root spanning from the
definition of the rational relative-root span. Mathlib's finite root-pairing
linear algebra then supplies coroot spanning. Reflection-invariant subspaces
give partitions of the actual roots whose root groups commute on every scheme
test; almost-simplicity makes each such partition empty or full. Nonemptiness
excludes the zero root space, and Mathlib's irreducibility constructor gives
the conclusion.

This is a derived proof from the published support in
[FullRelativeRootPairing](FullRelativeRootPairing.md),
[InvariantRootPartition](InvariantRootPartition.md) and
[RootCommutingPartition](RootCommutingPartition.md). The evaluation-pairing
hypothesis remains in the theorem's exact type; the stronger support theorem
does not need it. The proof uses neither the target proposition as a premise
nor any consumer of it, including the apartment affine-root comparisons. The
literature provenance of the target is recorded in
[RelativeRootSystemIrreducibleStatement](RelativeRootSystemIrreducibleStatement.md).
