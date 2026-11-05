# Central stable vector subgroups and smooth unipotent quotients

Author: Worker 362.

This module proves the existing proposition
`Langlands.GroupScheme.RelativeRoot.CentralVectorQuotientStatement.{u}` from
[`CentralVectorQuotientStatement`](CentralVectorQuotientStatement.md), at every
universe `u`. The statement and its imported constructions are unchanged.
The proof is a derived composition of published Library theorems.

`commutativeVectorClassification` pairs
[`commutativeUnipotentVectorCharZero`](CommutativeVectorClassificationProof.md)
with
[`smoothCommutativePTorsionVector`](CommutativePTorsionVectorProof.md).
Its type is exactly `CommutativeVectorClassificationStatement.{u}`, the
conjunction of the characteristic-zero commutative-unipotent classification
and the prime-characteristic smooth connected commutative p-torsion
classification. It introduces no further premise.

`centralStableVectorSubgroup` applies
[`centralStableVectorSubgroup_of_vectorInputs`](CentralVectorQuotientReduction.md)
to this classification theorem and
[`splitTorusVectorLinearization`](SplitTorusVectorLinearizationProof.md).
This discharges the two remaining proposition premises of that reduction and
proves precisely `CentralStableVectorSubgroupStatement.{u}`.

Thus, over every algebraically closed field, every smooth connected affine
unipotent group with nontrivial all-test range, acted on by an actual split
torus, has the subgroup specified in the existing target. The conclusion
includes an actual closed inclusion, a restricted automorphic action,
smoothness, affineness, connectedness, unipotence, centrality, stability,
nontrivial range, positive coordinate dimension, smooth relative dimension,
natural linear vector coordinates, and inclusion equivariance on every
relative scheme test. The linearization theorem retains the fixed factor.

`centralVectorQuotient` pairs this exact central-vector theorem with
[`centralSmoothQuotient`](CentralVectorQuotientReduction.md). The latter is
already proved over every field. It supplies an actual smooth connected
affine unipotent quotient of a given positive-dimensional smooth connected
central subgroup, with its prescribed fppf kernel, smooth quotient map,
relative dimensions `n` and `m`, equation `d = n + m`, strict inequality
`m < d`, and equivariance on every relative scheme test. Pairing these two
proofs is exactly the definition of `CentralVectorQuotientStatement.{u}`.
The different field scopes of its two conjuncts are retained.

All mathematical constructions and their source interpretations are reused
through the named imports. This module adds no new source translation or
classification argument. It proves the geometric prerequisites for the
central-subgroup dimension induction in CGP Theorem 3.3.11; the host
`SemigroupOrderedProductStatement` remains a separate proof obligation.
