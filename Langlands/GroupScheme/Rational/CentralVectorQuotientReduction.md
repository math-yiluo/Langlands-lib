# Central vector and quotient consequences of closed-subgroup unipotence

Author: Worker 362.

This internal derived unit supplies the published
[`unipotentClosedSubgroup`](../UnipotentClosedSubgroupProof.md) proof to the
existing central quotient and central-vector assemblies. Every declaration
retains arbitrary universe `u`.

`centralSmoothQuotient` has exactly the existing
`CentralSmoothQuotientStatement.{u}` as its type and has no structural
proposition premise. It applies
[`centralSmoothQuotient_of_closedSubgroup`](CentralSmoothQuotientOrbitReduction.md)
to `unipotentClosedSubgroup`. Thus it retains every field, group, inclusion,
action and dimension hypothesis of the published target. Its quotient is an
actual smooth connected affine unipotent group scheme with the specified
fppf kernel, smooth quotient map of relative dimension `n`, quotient dimension
`m`, equation `d = n + m`, strict inequality `m < d`, and equivariance on
every relative scheme test. The field need not be algebraically closed.

`centralStableVectorSubgroupOfVectorInputs` chooses the actual
`CentralStableVectorSubgroupData` supplied by
[`centralStableVectorSubgroupOfClassification`](CentralVectorClassificationReduction.md)
after filling its closed-subgroup-unipotence premise with the published
proof. It still assumes `CommutativeVectorClassificationStatement.{u}` and
`SplitTorusVectorLinearizationStatement.{u}`. As in that construction, the
field is algebraically closed, the ambient group is smooth connected affine
and unipotent with nontrivial actual all-test range, and the acting group is
a split torus with its actual automorphic action. The data retain the
commutative subgroup, natural linear vector coordinates, positive coordinate
dimension, smooth relative dimension, geometric connectedness, centrality,
stability, and equivariant inclusion, together with all the other fields of
the existing data structure.

`centralStableVectorSubgroup_of_vectorInputs` supplies the same published
proof to `centralStableVectorSubgroup_of_classification`, proving the exact
existing central-vector target under those two remaining proposition
premises. `centralVectorQuotient_of_vectorInputs` pairs this conditional
result with `centralSmoothQuotient`, yielding exactly
`CentralVectorQuotientStatement.{u}` under the same premises.

The provenance is composition of the named Library declarations; no new
source translation is involved. The two characteristic classification
results and whole-vector torus linearization remain proof obligations.
This unit supplies no unconditional central-vector existence theorem or
semigroup ordered-product theorem.
