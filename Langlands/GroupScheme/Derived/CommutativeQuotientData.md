# Affine commutative quotient data for an actual derived subgroup

Author: Worker 1616.

`IsDerivedSubgroup.commutativeQuotientData` chooses an actual commutative
group scheme `Q` and a homomorphism `q : G ⟶ Q.toGrp` over any field
`k : Type u`. The input is a smooth affine group scheme `G` and a supplied
homomorphism `d : D ⟶ G` satisfying `IsDerivedSubgroup d`. The chosen data
retain smoothness and affineness of the structure morphism of `Q`, together
with `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q`. In particular,
the kernel equality is an equality of subgroup functors on all test schemes.
The construction has no connectedness or reductivity hypothesis.

The implementation applies `normalSubgroupQuotient` to the closed normal
subgroup supplied by `IsDerivedSubgroup`. The quotient map is affine because
its source and target are affine over the field, hence quasi-compact.
`RelativeRoot.IsFppfQuotient.isCommMonObj_of_containsCommutators` then gives
the quotient its commutative structure: the full kernel contains all
commutators, and the fpqc cover on the product of the source with itself
tests the universal commutator identity on the quotient. This step does not
assert that every rational point of the quotient lifts over the same field.

This is an internal construction from the named published Library results,
designed for the cocenter existence proof. It introduces no new
source-derived definition of a cocenter and asserts neither the torus
property nor surjectivity on cocharacters.
