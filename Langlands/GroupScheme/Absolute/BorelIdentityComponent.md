# Borel conjugacy through the identity component

Worker 1358. This is an internal derived construction using the published
identity component and Borel transport results.

For a smooth affine group scheme `P` over a field `k`, the construction
`IsBorelSubgroup.identityComponentData` lifts an actual Borel embedding
`b : B ⟶ P` to an embedding `B ⟶ identityComponent P`. The lift is a Borel
embedding, and its composite with the identity-component inclusion is exactly
the original `b`. The source is unchanged.

`BorelSubgroupsAreConjugate.of_identityComponent` transfers actual rational
conjugacy of Borel embeddings from `P⁰` to `P`. In particular,
`borelSubgroupsAreConjugate_of_borelConjugacy` applies the explicitly assumed
`BorelConjugacyStatement` to the smooth affine connected group `P⁰` over an
algebraically closed field. This yields conjugacy of Borels of `P` without
assuming `P` connected. The statement of Borel conjugacy remains a premise;
this module does not prove it.

The second construction retains a specified torus in a closed overgroup.
Let `j : T.toGrp ⟶ G` be a maximal torus with `T` split, let `i : P ⟶ G`
be closed, and let `f : T.toGrp ⟶ P` satisfy `f ≫ i = j`. Assume `G` affine
and locally of finite type. If the Borels of `P` are rationally conjugate and
some ambient Borel factors through `P`, then
`BorelExistence.borelPairInOvergroupData` chooses:

- an actual group scheme `B` and an embedding `b : B ⟶ P`;
- an actual map `t : T.toGrp ⟶ B` satisfying `t ≫ b = f`;
- a proof that `b ≫ i` is a Borel of `G`.

`BorelPairInOvergroupData.isBorelPair` verifies that this chosen Borel and the
original `j` form a Borel pair. The overgroup `P` need not be connected or
reductive. The second construction itself works over every field; its
conjugacy premise can be supplied by the identity-component result over an
algebraically closed field when `P` is smooth affine.

## Implemented proof and provenance

A Borel has connected source, so the published
`IdentityComponent.factor` factors it through the open and closed inclusion
`P⁰ ⟶ P`. The factorization identity and
`IsBorelSubgroup.of_comp` prove that the factor is a Borel of `P⁰`. Conjugacy
in `P⁰` is then transported by `SubgroupConjugate.postcomp` along `P⁰ ⟶ P`.
This preserves the actual conjugating isomorphism and maps the conjugating
point to a point of `P`.

For the torus construction, the published containing-Borel theorem produces
a Borel of `P` containing the original map `f`. The promotion theorem
`BorelSubgroupsAreConjugate.isBorelSubgroup_comp` makes it an ambient Borel,
using the assumed existence of one ambient Borel in `P`. Associativity and the
two recorded factorization identities give the Borel-pair identity.

All conclusions follow from these proved constructions and the displayed
premises. No literature assertion is added. In particular, no parabolic
connectedness, maximal-torus conjugacy, regular-cocharacter Borel theorem,
or parabolic classification is assumed implicitly or proved here.
