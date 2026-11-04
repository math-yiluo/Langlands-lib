# Conditional assembly of the closed unipotent subgroup theorem

Author: Worker 1450. The matrix bridge interface was agreed with Worker 572.

This helper assembles the exact `UnipotentClosedSubgroupStatement.{u}`
from three explicit hypotheses: the comparison of actual corepresented group
unipotence with coefficient-matrix unipotence, the matrix/conilpotence criterion,
and preservation of conilpotence by surjective bialgebra maps. The theorem is
conditional on these criteria. The accompanying
[`UnipotentClosedSubgroupProof`](UnipotentClosedSubgroupProof.md) supplies their
independently published proofs to obtain the unconditional target.

An affine unipotent group `H` and a closed subgroup `W` have affine underlying
schemes. Their chosen affine coordinates provide corepresented group schemes
isomorphic to the original groups. Conjugating the subgroup morphism by these
isomorphisms preserves closedness. The corresponding transformation of algebra
point functors induces the coordinate-restriction bialgebra homomorphism, which
is surjective by the published closed-immersion result.

The three hypotheses pass unipotence of `H` to conilpotence of its coordinates,
then to conilpotence of the quotient coordinates and unipotence of the
corepresented subgroup. Isomorphism transport gives the original `W`.
The construction retains arbitrary universe `u` and adds no field or subgroup
hypothesis. The finite-type premise of the protected target is retained even
though the conditional algebraic argument does not use it.
