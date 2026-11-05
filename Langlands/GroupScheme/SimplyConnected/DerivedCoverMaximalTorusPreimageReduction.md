# Reduction of full derived-cover torus preimages

Author: Worker 1614, using Worker 1669's full-pullback comparison.

`DerivedCoverMaximalTorusPreimageReductionStatement.{u}` is the implication
from two existing structural statements to the exact
`DerivedCoverMaximalTorusPreimageStatement.{u}`.
`derivedCoverMaximalTorusPreimage_of_structuralInputs` proves this
implication. Both
`MaximalTorusCentralizerStatement` and `DerivedMaximalSplitTorusStatement`
remain explicit assumptions; this module does not prove either statement.

Over an algebraically closed field, every torus is split by the published
finite Galois splitting theorem. The assumed derived statement supplies
a maximal split torus in the derived subgroup that factors into the
given ambient maximal torus. It is a maximal torus because every torus
over that field is split. The proved split-maximal-torus lifting theorem
for central isogenies then supplies a maximal torus in the source and
the required factorization into the ambient torus.

For an arbitrary original field, connected reductivity of all three
groups is preserved under field extension. The full derived subgroup
and the central isogeny also base change by their published theorems.
The assumed self-centralizer statement for the original maximal torus
makes its extension maximal through the published all-test
self-centralizer base-change argument. The algebraically closed argument
then supplies a closed source torus, and the same assumed
self-centralizer statement makes it self-centralizing in the source.
No base-change theorem for algebraic simple connectedness is needed.

The full pullback after algebraic closure centralizes this source torus.
Indeed, its image and the source torus's image both factor through the
commutative ambient torus. The closed derived inclusion reflects their
commutation, and `IsCentralIsogeny.torusCentralizer_comap` reflects
centralization through the central isogeny on every test scheme.
Worker 1669's
`isTorus_subgroupIntersection_of_selfCentralizing_of_reflection`
constructs an isomorphism of this actual pullback with the source torus.
It follows that the full pullback is a torus, including all its
scheme structure. `subgroupIntersectionBaseChangeIso` identifies it with
the base change of the original pullback, and `IsTorus.of_baseChange`
descends the torus property.

The final conclusion retains every field, arbitrary universe, the
original derived cover and maximal torus hypotheses, and the original
full scheme-theoretic pullback. No characteristic, perfectness,
smooth-cover or reducedness premise is added. This is a conditional
intermediate result, rather than an unconditional proof of the task's
target: the two displayed structural statements still require proofs.

The provenance is internal: this combines the cited Library interfaces
and keeps the two outstanding structural assertions as hypotheses.
