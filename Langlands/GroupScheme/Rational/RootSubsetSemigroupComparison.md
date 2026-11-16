# Root-generated unipotent groups and semigroup subgroups

These are internal consequences of published Library interfaces used in the
proof of Borel–Tits 3.22 c). They are not separate claims attributed to an
original source.

`IsUnipotentRootSubset.zero_notMem_addSubsemigroupClosure` uses the Weyl
translate of a positive root set in the definition of a unipotent root
subset. The Weyl-transformed cocharacter pairs positively with every chosen
root, by invariance of the character–cocharacter pairing. The strictly
positive pairing region is an additive semigroup, so the generated
semigroup lies there and cannot contain zero.

`IsRootSubsetUnipotentGroup.range_eq_semigroupSubgroup` assumes that a
zero-excluding character semigroup selects exactly the chosen relative
roots, and retains the split-torus, smooth affine group and opposite
factor-pair hypotheses of the published selected-root product theorem.
Every chosen root group lies in the semigroup subgroup by its cyclic-tail
description. Semigroup realization and the defining closed-subgroup
minimality give one inclusion. For the other inclusion, the published
all-test selected-root generation theorem expresses the semigroup subgroup
on every test scheme as the supremum of its selected root groups. Each
such root group lies in the given closed group.

The final two lemmas apply the same defining minimality to inclusions of
root sets, giving inclusion between their root-generated unipotent groups,
or inclusion of a root-generated unipotent group in a group also generated
by the torus centralizer. All of these range equalities and inclusions hold
on every test scheme.
