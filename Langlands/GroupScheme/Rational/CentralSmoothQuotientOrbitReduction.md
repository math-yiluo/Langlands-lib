# Actual unipotent quotients using the published closed-orbit theorem

Author: Worker 362.

This derived module uses the published
[`unipotentAffineOrbitClosed`](../UnipotentAffineOrbitClosedProof.md) and
[`unipotentFieldExtensionStatement`](../Reductive/UnipotentFieldExtensionProof.md)
theorems to construct actual affine homogeneous and normal quotients over
every field `k : Type u`. Neither theorem remains an input here.

`Chevalley.unipotentAffineQuotientOfUnipotentSubgroup` takes a smooth affine
group scheme `G` with `IsUnipotent G`, a group scheme `H`, and an actual
closed inclusion `i : H ⟶ G`. It also takes smoothness and unipotence of
`H`. It constructs
`HomogeneousQuotientFromEmbedding.AffineHomogeneousQuotient i`: an actual
affine homogeneous quotient, with its smooth surjective quasi-compact
projection and its right-coset fiber characterization on every relative
scheme test. Connectedness and normality of either group are unnecessary
for this constructor.

The closed inclusion and affineness of `G` imply affineness of `H`.
The published `IsUnipotent.baseChange` then proves unipotence of both
groups after extension to `AlgebraicClosure k`. Applying
[`unipotentAffineQuotientOfFieldExtension`](../Chevalley/UnipotentQuotientDescent.md)
with these two proofs and the published closed-orbit theorem supplies
the actual affine quotient over the original field. This uses the
existing field-extension descent construction, so no perfectness,
characteristic or separability restriction is introduced.

`Chevalley.exists_unipotentNormalQuotient_overField` assumes further that
`G` is connected, that the actual range of `i : Z ⟶ G` is normal and
stable under a supplied automorphic action of any group scheme `A`, and
that `G` and `Z` have smooth relative dimensions `d` and `n`, with `0 < n`.
It retains `IsUnipotent Z` as an explicit hypothesis. It constructs an
actual group scheme `Q`, homomorphism `q : G ⟶ Q`, descended action and
natural number `m`. The group `Q` is affine, smooth, connected and
unipotent. Its fppf quotient kernel is exactly `SubgroupFunctor.range i`,
the map `q` is smooth of relative dimension `n`, and `Q` is smooth of
relative dimension `m`, with `d = n + m` and `m < d`. Equivariance holds
on every relative scheme test. The proof uses the preceding constructor
and `HomogeneousQuotient.exists_action_relativeDimension`; it imposes no
splitness or centrality condition on the subgroup or acting group.

`RelativeRoot.centralSmoothQuotient_of_closedSubgroup` proves the exact
existing `CentralSmoothQuotientStatement.{u}` from only
`UnipotentClosedSubgroupStatement.{u}`. It supplies the two published
theorems to
[`centralSmoothQuotient_of_structuralStatements`](CentralSmoothQuotientReduction.md).
Thus every field, group, inclusion, action and dimension quantifier of
the central target is retained, as are its actual fppf kernel, all-test
equivariance and strict dimension decrease.

The provenance is internal and derived: each construction applies the
published quotient, descent, closed-orbit and unipotence declarations
by their Lean names. This module does not prove the remaining
closed-subgroup unipotence proposition, central stable vector-subgroup
existence or `SemigroupOrderedProductStatement`.
