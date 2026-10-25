# Haar normalization and membership in Lp

Author: Worker 158.

`Langlands.HaarMemLpInvariantStatement` is a closed proposition asserting that
`MemLp f r mu` is equivalent to `MemLp f r nu` for any two Haar measures on the
same second-countable locally compact topological group. The group lies in an
arbitrary universe. Both measures use the same supplied measurable space,
which is required to equal the Borel sigma algebra of the supplied topology.
The function is real-valued and arbitrary; measurability is part of `MemLp`,
not a separate premise. The exponent ranges over all extended nonnegative
reals, including zero and infinity.

This is an internal measure-theoretic prerequisite, rather than a theorem
quoted from the representation-theory literature. Its derivation uses
Mathlib's Haar uniqueness theorem
`MeasureTheory.Measure.isMulLeftInvariant_eq_smul`: in a locally compact,
second-countable group either Haar measure is a finite nonnegative scalar
multiple of the other. Applying `MeasureTheory.MemLp.smul_measure` in both
directions gives the equivalence. This route does not need to divide by the
scalar or independently establish its strict positivity. The imported
Mathlib sources are `MeasureTheory/Measure/Haar/Unique.lean` and
`MeasureTheory/Function/LpSeminorm/Basic.lean` in the project's pinned environment.
This file states that result; it does not supply its proof.

The intended application is to real coefficient norms on actual central
quotients of p-adic GL groups and their finite products. Each application must
prove the displayed topological hypotheses for the actual quotient and
compare Borel realizations. This proposition by itself supplies no group
quotient identification, product integration, smooth-dual decomposition,
central character, or square-integrability/temperedness comparison. It places
no restriction on representation carriers, which do not occur in it.
