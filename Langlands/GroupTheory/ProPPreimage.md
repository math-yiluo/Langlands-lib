# Inverse images of p-subgroups under maps with pro-p kernels

This internal module supplies the group-theoretic lifting step for finite
reductive reduction maps. It uses the existing
`Langlands.Cohomology.IsProPSubgroup` predicate with induced subgroup
topologies; the source and target groups may have independent universes.

For an abstract homomorphism `f : G →* Q` whose kernel is pro-p,
`IsProPSubgroup.comap_of_isPGroup` proves that the inverse image
`P.comap f` of a p-subgroup `P` is pro-p, provided that this inverse image
is compact and totally disconnected. This theorem requires no topology
on `Q` and no surjectivity or finiteness hypothesis.

The proof restricts `f` to the homomorphism
`P.comap f →* P` supplied by Mathlib's `MonoidHom.subgroupComap`.
Its kernel is `f.ker.subgroupOf (P.comap f)`. The subgroup transport lemma
makes this restricted kernel pro-p without changing its topology.
The first isomorphism theorem identifies the quotient by that kernel
with a subgroup of `P`, which is a p-group. The pro-p extension theorem
then proves the claim.

When `Q` is given a discrete topology and `f` is continuous,
`discretePreimageOpenSubgroup` bundles `P.comap f` as an open subgroup.
Openness follows by pulling back the open subset `P` of `Q`.

`IsProPSubgroup.isOpen_and_comap_of_isPGroup` specializes the first
theorem to a compact totally disconnected topological group `G` and
a continuous map to a discrete group `Q`. Every inverse-image subgroup
is open, hence closed and compact. Total disconnectedness is inherited
from `G`, so the theorem gives both openness and the pro-p property.
The kernel's pro-p property is still an explicit hypothesis.

The provenance is the elementary kernel identification, the first
isomorphism theorem and the pro-p transport and extension lemmas.
No external classification theorem is used. Applications to a
parahoric reduction must still identify the actual kernel, prove it
pro-p, and prove continuity of the reduction map. The module proves
neither the finite reductive Sylow classification nor the full corrected
KP Proposition 13.5.2.
